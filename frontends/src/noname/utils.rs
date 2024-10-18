use std::collections::HashMap;

use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, R1CSVar};
use ark_relations::r1cs::SynthesisError;
use noname::inputs::JsonInputs;
use serde_json::json;

pub struct NonameInputs(pub JsonInputs);

impl<F: PrimeField> From<(&Vec<F>, String)> for NonameInputs {
    fn from(value: (&Vec<F>, String)) -> Self {
        let (values, key) = value;
        let mut inputs = HashMap::new();
        if values.is_empty() {
            NonameInputs(JsonInputs(inputs))
        } else {
            let field_elements: Vec<String> = values
                .iter()
                .map(|value| {
                    if value.is_zero() {
                        "0".to_string()
                    } else {
                        value.to_string()
                    }
                })
                .collect();
            inputs.insert(key, json!(field_elements));
            NonameInputs(JsonInputs(inputs))
        }
    }
}

impl NonameInputs {
    pub fn from_fpvars<F: PrimeField>(
        value: (&Vec<FpVar<F>>, String),
    ) -> Result<Self, SynthesisError> {
        let (values, key) = value;
        let mut inputs = HashMap::new();
        if values.is_empty() {
            Ok(NonameInputs(JsonInputs(inputs)))
        } else {
            let field_elements: Vec<String> = values
                .iter()
                .map(|var| {
                    let value = var.value()?;
                    if value.is_zero() {
                        Ok("0".to_string())
                    } else {
                        Ok(value.to_string())
                    }
                })
                .collect::<Result<Vec<String>, SynthesisError>>()?;
            inputs.insert(key, json!(field_elements));
            Ok(NonameInputs(JsonInputs(inputs)))
        }
    }
}
