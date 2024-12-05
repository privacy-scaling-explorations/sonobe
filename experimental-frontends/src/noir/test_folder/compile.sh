#!/bin/bash
CUR_DIR=$(pwd)
TEST_PATH="${CUR_DIR}/experimental-frontends/src/noir/test_folder/"
for test_path in test_circuit test_mimc test_no_external_inputs; do
	FOLDER="${TEST_PATH}${test_path}/"
	cd ${FOLDER} && nargo compile && cd ${TEST_PATH}
done
