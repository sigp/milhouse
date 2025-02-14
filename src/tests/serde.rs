use crate::{List, Vector};
use typenum::U4;

#[test]
fn deserialize_list_invalid_length() {
    let json = serde_json::json!([1, 2, 3, 4, 5]);
    let result: Result<List<u64, U4>, _> = serde_json::from_value(json);
    assert!(result.is_err());

    let json = serde_json::json!([1, 2, 3]);
    let result: Result<List<u64, U4>, _> = serde_json::from_value(json);
    assert!(result.is_ok());

    let json = serde_json::json!([1, 2, 3, 4]);
    let result: Result<List<u64, U4>, _> = serde_json::from_value(json);
    assert!(result.is_ok());
}

#[test]
fn deserialize_vector_invalid_length() {
    let json = serde_json::json!([1, 2, 3, 4, 5]);
    let result: Result<Vector<u64, U4>, _> = serde_json::from_value(json);
    assert!(result.is_err());

    let json = serde_json::json!([1, 2, 3]);
    let result: Result<Vector<u64, U4>, _> = serde_json::from_value(json);
    assert!(result.is_err());

    let json = serde_json::json!([1, 2, 3, 4]);
    let result: Result<Vector<u64, U4>, _> = serde_json::from_value(json);
    assert!(result.is_ok());
}
