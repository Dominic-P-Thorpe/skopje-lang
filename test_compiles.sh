RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

successes=0
fails=0

> test_log.txt
echo "Starting compilation tests..."

for file in tests/should_pass/*.skj; do
    echo "compiling $file"
    cargo run "$file" test_out.cpp &>> temp_log
    g++ "test_out.cpp" -std=c++20 2>> test_log.txt
    
    if [ $? -ne 0 ]; then 
        echo -e "${RED}$file failed to compile!${NC}"
        fails=$((fails+1))
    else
        echo -e "${GREEN}$file compiled successfully!${NC}"
        successes=$((successes+1))
    fi 
done

total=$((successes + fails))

rm temp_log
echo -e "Compilation tests complete: Total: ${total}, ${GREEN}${successes} passed${NC}, ${RED}${fails} failed${NC}"
