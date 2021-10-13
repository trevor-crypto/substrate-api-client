use sp_application_crypto::Ss58Codec;
use sp_runtime::AccountId32;
use substrate_api_client::rpc::json_req::author_submit_extrinsic;
use substrate_api_client::{
    Api, ApiClientError, ApiResult, FromHexString, Hash, RpcClient, Value, XtStatus,
};
struct MyClient {
    // pick any request crate, such as ureq::Agent
    inner: ureq::Agent,
}

impl MyClient {
    pub fn new() -> Self {
        Self {
            inner: ureq::agent(),
        }
    }

    pub fn send_json(&self, _path: &str, json: Value) -> Result<Value, Box<dyn std::error::Error>> {
        let path = "https://westend-rpc.polkadot.io";
        let response = self
            .inner
            .post(&path)
            .send_json(json)?
            .into_json::<Value>()?;
        Ok(response)
    }
}

impl RpcClient for MyClient {
    fn get_request(&self, jsonreq: serde_json::Value) -> ApiResult<String> {
        self.send_json("".into(), jsonreq)
            .map(|v| v.get("result").unwrap().to_string())
            .map_err(|err| ApiClientError::RpcClient(err.to_string()))
    }

    fn send_extrinsic(
        &self,
        xthex_prefixed: String,
        _exit_on: XtStatus,
    ) -> ApiResult<Option<Hash>> {
        let jsonreq = author_submit_extrinsic(&xthex_prefixed);
        let res: String = self
            .send_json("".into(), jsonreq)
            .map(|res| res.to_string())
            .map_err(|err| ApiClientError::RpcClient(err.to_string()))?;
        Ok(Some(Hash::from_hex(res)?))
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = MyClient::new();
    let api = Api::<(), _>::new(client)?;
    let acct = AccountId32::from_ss58check_with_version(
        "5Hq465EqSK865f4cHMgDpuKZf45ukuUshFxAPCCzmJEoBoNe",
    )
    .unwrap();
    let res = api.get_account_data(&acct.0)?;
    dbg!(res);

    Ok(())
}
