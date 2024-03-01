//! Module containing concept of an Ethereum RPC batches.
//!
//! Currently, this implementation is a bit hacky, and I'm not 100% satisfied
//! with how the typing turned out, but it is somewhat ergonomic to use.
//! Specifically, the generic types here make quite a few assumptions and aren't
//! entirely generic.

use crate::{
    jsonrpc::{self, Id, JsonError, Request, Response},
    method::Method,
};
use std::future::Future;
use thiserror::Error;

/// Executes a batch of JSON RPC calls with the provided roundtrip
/// implementation.
pub fn call<B, F, E>(batch: B, roundtrip: F) -> Result<B::Values, E>
where
    B: Batch,
    F: FnOnce(Vec<Request>) -> Result<Vec<Response>, E>,
    E: From<Error> + From<jsonrpc::Error> + From<JsonError>,
{
    let results = try_call(batch, roundtrip)?;
    let values = B::values(results)?;
    Ok(values)
}

/// Executes a batch of JSON RPC calls with the provided `async` roundtrip
/// implementation.
pub async fn call_async<B, F, Fut, E>(batch: B, roundtrip: F) -> Result<B::Values, E>
where
    B: Batch,
    F: FnOnce(Vec<Request>) -> Fut,
    Fut: Future<Output = Result<Vec<Response>, E>>,
    E: From<Error> + From<jsonrpc::Error> + From<JsonError>,
{
    let results = try_call_async(batch, roundtrip).await?;
    let values = B::values(results)?;
    Ok(values)
}

/// Executes a batch of JSON RPC calls with the provided roundtrip
/// implementation.
///
/// Returns the individual JSON RPC results for each request. This allows fine-
/// grained error handing for individual calls.
pub fn try_call<B, F, E>(batch: B, roundtrip: F) -> Result<B::Results, E>
where
    B: Batch,
    F: FnOnce(Vec<Request>) -> Result<Vec<Response>, E>,
    E: From<Error> + From<JsonError>,
{
    let (requests, ids) = requests(batch)?;
    let responses = roundtrip(requests)?;
    results::<B, E>(ids, responses)
}

/// Executes a batch of JSON RPC calls with the provided `async` roundtrip
/// implementation.
///
/// Returns the individual JSON RPC results for each request. This allows fine-
/// grained error handing for individual calls.
pub async fn try_call_async<B, F, Fut, E>(batch: B, roundtrip: F) -> Result<B::Results, E>
where
    B: Batch,
    F: FnOnce(Vec<Request>) -> Fut,
    Fut: Future<Output = Result<Vec<Response>, E>>,
    E: From<Error> + From<JsonError>,
{
    let (requests, ids) = requests(batch)?;
    let responses = roundtrip(requests).await?;
    results::<B, E>(ids, responses)
}

fn requests<B>(batch: B) -> Result<(Vec<Request>, Vec<Id>), JsonError>
where
    B: Batch,
{
    let requests = batch.into_requests()?;
    let ids = requests.iter().map(|request| request.id).collect();
    Ok((requests, ids))
}

fn results<B, E>(ids: Vec<Id>, mut responses: Vec<Response>) -> Result<B::Results, E>
where
    B: Batch,
    E: From<Error> + From<JsonError>,
{
    if ids.len() != responses.len() || responses.iter().any(|response| response.id.is_none()) {
        return Err(Error.into());
    }

    responses.sort_unstable_by_key(|response| response.id.unwrap().0);
    if responses
        .iter()
        .zip(ids)
        .any(|(response, id)| response.id.unwrap() != id)
    {
        return Err(Error.into());
    }

    let results = B::from_responses(responses)?;
    Ok(results)
}

/// A trait defining a batch Ethereum RPC requests.
pub trait Batch {
    type Results;
    type Values;

    fn into_requests(self) -> Result<Vec<Request>, JsonError>;
    fn from_responses(responses: Vec<Response>) -> Result<Self::Results, JsonError>;
    fn values(results: Self::Results) -> Result<Self::Values, jsonrpc::Error>;
}

macro_rules! impl_batch_for_tuple {
    ($($m:ident),*) => {
        impl<$($m,)*> Batch for ($(($m, <$m>::Params),)*)
        where
            $($m: Method,)*
        {
            type Results = ($(Result<<$m>::Result, jsonrpc::Error>,)*);
            type Values = ($(<$m>::Result,)*);

            fn into_requests(self) -> Result<Vec<Request>, JsonError> {
                #[allow(non_snake_case)]
                let ($($m,)*) = self;
                Ok(vec![
                    $(Request::new($m.0, $m.1)?,)*
                ])
            }

            fn from_responses(responses: Vec<Response>) -> Result<Self::Results, JsonError> {
                #[allow(unused_mut, unused_variables)]
                let mut responses = responses.into_iter();
                Ok((
                    $(responses.next().unwrap().result::<$m>()?,)*
                ))
            }

            fn values(results: Self::Results) -> Result<Self::Values, jsonrpc::Error> {
                #[allow(non_snake_case)]
                let ($($m,)*) = results;
                Ok(($($m?,)*))
            }
        }
    };
}

impl_batch_for_tuple!();
impl_batch_for_tuple!(M0);
impl_batch_for_tuple!(M0, M1);
impl_batch_for_tuple!(M0, M1, M2);
impl_batch_for_tuple!(M0, M1, M2, M3);
impl_batch_for_tuple!(M0, M1, M2, M3, M4);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8, M9);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, Ma);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, Ma, Mb);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, Ma, Mb, Mc);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, Ma, Mb, Mc, Md);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, Ma, Mb, Mc, Md, Me);
impl_batch_for_tuple!(M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, Ma, Mb, Mc, Md, Me, Mf);

impl<M, const N: usize> Batch for [(M, M::Params); N]
where
    M: Method,
{
    type Results = [Result<M::Result, jsonrpc::Error>; N];
    type Values = [M::Result; N];

    fn into_requests(self) -> Result<Vec<Request>, JsonError> {
        self.into_iter()
            .map(|(method, params)| Request::new(method, params))
            .collect()
    }

    fn from_responses(responses: Vec<Response>) -> Result<Self::Results, JsonError> {
        Ok(responses
            .into_iter()
            .map(Response::result::<M>)
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .unwrap_or_else(|_| panic!("incorrect length")))
    }

    fn values(results: Self::Results) -> Result<Self::Values, jsonrpc::Error> {
        Ok(results
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .unwrap_or_else(|_| panic!("incorrect length")))
    }
}

impl<M> Batch for Vec<(M, M::Params)>
where
    M: Method,
{
    type Results = Vec<Result<M::Result, jsonrpc::Error>>;
    type Values = Vec<M::Result>;

    fn into_requests(self) -> Result<Vec<Request>, JsonError> {
        self.into_iter()
            .map(|(method, params)| Request::new(method, params))
            .collect()
    }

    fn from_responses(responses: Vec<Response>) -> Result<Self::Results, JsonError> {
        responses.into_iter().map(Response::result::<M>).collect()
    }

    fn values(results: Self::Results) -> Result<Self::Values, jsonrpc::Error> {
        results.into_iter().collect()
    }
}

#[derive(Clone, Copy, Debug, Default, Error, PartialEq)]
#[error("JSON RPC batch responses do not match requests")]
pub struct Error;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        eth,
        types::{BlockTag, Empty, Hydrated, TransactionReceiptKind},
    };
    use serde_json::json;

    fn roundtrip(
        calls: serde_json::Value,
        results: serde_json::Value,
    ) -> impl FnOnce(Vec<Request>) -> Result<Vec<Response>, Box<dyn std::error::Error>> {
        move |requests| {
            for (call, request) in calls.as_array().unwrap().iter().zip(&requests) {
                assert_eq!(
                    call,
                    &json!({
                        "method": request.method,
                        "params": request.params,
                    }),
                );
            }
            let serde_json::Value::Array(results) = results else {
                panic!()
            };
            let responses = requests
                .iter()
                .zip(results)
                .map(|(request, result)| Response {
                    jsonrpc: jsonrpc::Version::V2,
                    result: Ok(jsonrpc::Value(result)),
                    id: Some(request.id),
                })
                .collect();
            Ok(responses)
        }
    }

    #[test]
    fn batch_request() {
        let (
            latest, 
            safe,
            receipts
        ) = call(
            (
                (eth::BlockNumber, Empty),
                (eth::GetBlockByNumber, (BlockTag::Safe.into(), Hydrated::Yes)),
                (eth::GetBlockReceipts, (18_460_382.into(),)),
            ),
            roundtrip(
                json!([
                    { "method": "eth_blockNumber", "params": [] },
                    { "method": "eth_getBlockByNumber", "params": ["safe", true] },
                    { "method": "eth_getBlockReceipts", "params": ["0x119aede"] },
                ]),
                serde_json::from_str(
                    r#"[
                      "0x1163fd1",
                      {
                        "baseFeePerGas": "0xb7bd4ece6",
                        "difficulty": "0x30f9a5c24b37e8",
                        "extraData": "0x75732d77657374312d38",
                        "gasLimit": "0x1ca35d2",
                        "gasUsed": "0xc05fcf",
                        "hash": "0x0950f85eb900296a98747b00ff2acfdeb1e5dba5060ee3fd25b83aaec6b24215",
                        "logsBloom": "0x5d32840202020937554098c4b210833104680b9366c803640c74b0c80058114e0042c3cc11824470b40c50f0068f0783031a421a2b0fb9245250ac01302825889908960070244828a8c327aa8984602501472c8cc1630c988e435e218300601713a900d08e624e861f0408b901418fb02724001ced0886a954b5141dc07a0d891234490302225447108a030120840570352caa4131a6405a28e009505314c480af122327b3e0e91e06000b860e8a448040158e2923c3058a6162806454cae51c7120e683404b0c17450626c4085e330026f5bacd40082998ca000f8e18792010a038628a01100283270a0030396b59208870084534dc40e2004539a22b109e27",
                        "miner": "0xea674fdde714fd979de3edf0f56aa9716b898ec8",
                        "mixHash": "0x2795bc665f9ccdffd3d8ef28b29401cad05a5f4ffe88acf206c0f6d06880ebd2",
                        "nonce": "0xedb67ceba7323a68",
                        "number": "0xe4e364",
                        "parentHash": "0x7436cc9a28f3ab1265a252ba36d5d7042641369043a140e99e43bff98d58f015",
                        "receiptsRoot": "0x07c332da0afbe0a02195af3fe91445f785b7ec96e149e83eb959ab2127d8b396",
                        "sha3Uncles": "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347",
                        "size": "0xdf00",
                        "stateRoot": "0xcdcfa6bb77e0364841d015b1e84fafcd0c3f8ed1db959f0bb2c38c287c6aea9a",
                        "timestamp": "0x62b147f5",
                        "totalDifficulty": "0xb0e7fa732d136d6e1f4",
                        "transactions": [
                            {
                                "blockHash": "0x0950f85eb900296a98747b00ff2acfdeb1e5dba5060ee3fd25b83aaec6b24215",
                                "blockNumber": "0xe4e364",
                                "from": "0x475ef7c1493bb29642529c30ad9bd4d1f27aed98",
                                "gas": "0xc05a",
                                "gasPrice": "0xba43b7400",
                                "maxPriorityFeePerGas": "0x9502f900",
                                "maxFeePerGas": "0xba43b7400",
                                "hash": "0x20ea0eb2a3a3928ccfa86246fdf5f1f4ddd8c98a04f67ace5e149e22ecfe6b3a",
                                "input": "0xa22cb4650000000000000000000000001e0049783f008a0085193e00003d00cd54003c710000000000000000000000000000000000000000000000000000000000000001",
                                "nonce": "0x26a",
                                "to": "0x2ee6af0dff3a1ce3f7e3414c52c48fd50d73691e",
                                "transactionIndex": "0x87",
                                "value": "0x0",
                                "type": "0x2",
                                "accessList": [],
                                "chainId": "0x1",
                                "v": "0x0",
                                "r": "0x269746c7467dcb8d6535ff2ec3cc2257872bd9f55564b1b364e750263f831902",
                                "s": "0x2c391ac90acdd9cf0f4e28f3647a9be74b05a7b261a83c0ae8199c733012a415"
                              }
                        ],
                        "transactionsRoot": "0xfe498a1338059330121151a24a01070321a63bbd2c82607ae747a26cd493e141",
                        "uncles": []
                      },
                      [
                        {
                            "blockHash": "0x79313e7f7904f21e3e3f0abced0cd95b154bca0b4d0c4a5ddfbc70442c7f7205",
                            "blockNumber": "0x119aede",
                            "contractAddress": null,
                            "cumulativeGasUsed": "0xf0c1",
                            "effectiveGasPrice": "0x2bfe06c9d",
                            "from": "0xa3b458db8381dcc1fc4529a41ebe2804b07e7ef6",
                            "gasUsed": "0xf0c1",
                            "logs": [],
                            "logsBloom": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
                            "status": "0x0",
                            "to": "0x49048044d57e1c92a77f79988d21fa8faf74e97e",
                            "transactionHash": "0xdf3aa03889d1de2f198f31ccaeeb83019c2f9140cad911011a9d4d2849157393",
                            "transactionIndex": "0x0",
                            "type": "0x3",
                            "blobGasUsed": "0x123",
                            "blobGasPrice": "0x12345"
                        }
                      ]
                    ]"#,
                )
                .unwrap(),
            ),
        )
        .unwrap();
        assert_eq!(
            receipts.unwrap()[0].kind,
            TransactionReceiptKind::Eip4844 {
                blob_gas_used: 291_u64.into(),
                blob_gas_price: 74_565_u64.into(),
            }
        );
        assert_eq!(latest, 0x1163fd1);
        assert_eq!(safe.unwrap().number, 0xe4e364);
    }
}
