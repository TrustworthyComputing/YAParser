#include <string>
#include <vector>
#include <algorithm>
#include <iostream>
#include <map>
#include <stack>
#include <ctype.h>
#include <fstream>
#include <stdio.h>
#include <sstream>
#include <regex>
#include <iterator>
#include <boost/algorithm/string/trim.hpp>
#include "stdc++.h"
#include <ctype.h>

using namespace std;

vector<string> split(string str, char separator) {
    vector<string> tokens;
    int startIndex = 0, endIndex = 0;
    for (int i = 0; i <= str.size(); i++) {
        // If we reached the end of the word or the end of the input.
        if (str[i] == separator || i == str.size()) {
            endIndex = i;
            string temp;
            temp.append(str, startIndex, endIndex - startIndex);
            tokens.push_back(temp);
            startIndex = endIndex + 1;
        }
    }
    return tokens;
}

bool is_number(const string &s) {
    string::const_iterator it = s.begin();
    while (it != s.end() && isdigit(*it))
        ++it;
    return !s.empty() && it == s.end();
}

class Parser {
private:
    /// a map of string and integer to keep track of the indices of the variables to be defined.
    map<string, int> vars_indx;
    /// An iterator over the vars_indx map
    map<string, int>::iterator it;
    /// variables counter -- start from index 2 as index 0 is reserved for 1 and index 1 is reserved for 1.
    int vars_cntr;

    int res_cntr;
    /// The operations to be computed: +, *, -
    string op;
    /// The integer representation of operand 1
    int op1;
    /// The index of operand 1 to be stored in the vars_indx map
    int op1_indx;
    /// Operand 1 as read from the IR
    string op1_tmp;
    /// The integer representation of operand 2
    int op2;
    /// The index of operand 2 to be stored in the vars_indx map
    int op2_indx;
    /// Operand 2 as read from IR
    string op2_tmp;
    /// The index to which a result is stored as read from the IR (e.g., '0, '1, etc.)
    string res_indx_tmp;
    /// the integer representation of the result index
    int res_indx;

    /// A flag to indicate that the value to read from the IR is an array index.
    bool arr_flag;
    /// A map to store the array index label (string) and index value (int).
    map<string, int> arr_indx;

    /// It means the result of the next computation is an index in array, so store it in the arr_indx map.
    bool next_is_indx = false;
    string indx_lbl_arr_indx;

    /// When we access a value from an array, we need to tell if the value is the first operand or the second operand.
    bool is_op1 = true;

    /// When we are storing values in an array, the IR uses consequetive calls of "store" instruction. The first store instruction has the array label in
    /// in which we are storing the values. Next "store" instructions reference the previous store instruction; this like a recursive call until we reach the
    /// target array. We use this flag to differentiate between the first "store" instruction and the others. If this is the first, then it references the target
    /// array, otherwise, we igonre the array label provided with it and use the we save in the variable "store_array_lbl" below.
    bool first_store_inst = true;

    string store_array_lbl;

    /// This map is used as an evaluted table of the compuation, it is similar to print of the arithimtic circuit (cir_print), but without variables
    /// on the right-hand side of the equation. For example, if we have cir_print = $r3:=1, r4:=2, $r5:=r3+r4, then the table will have: $r3:=1, r4:=2, $r5:=3.
    map<string, int> eval_table;

    /// For perfroming the equlaity check, we will use fermat's little theorem: we subtract the two values, then exponentiate to plaintext modulus set in SEAL.
    /// It should be a prime number, so assume it is 19 (It should be modified in modified in SEAL and Rino.)
    int ptxt_mod = 13;

    /// A flag to indicate if we processing if-then-else statement.
    bool ite_flg = 0;

    vector<string> split(string str, char separator) {
        vector<string> tokens;
        int startIndex = 0, endIndex = 0;
        for (int i = 0; i <= str.size(); i++) {
            // If we reached the end of the word or the end of the input.
            if (str[i] == separator || i == str.size()) {
                endIndex = i;
                string temp;
                temp.append(str, startIndex, endIndex - startIndex);
                tokens.push_back(temp);
                startIndex = endIndex + 1;
            }
        }
        return tokens;
    }

    bool isStringEmptyOrWhitespace(const std::string &str) {
        // Check if the string is empty
        if (str.empty()) {
            return true;
        }

        // Check if all characters in the string are whitespace
        return std::all_of(str.begin(), str.end(), [](unsigned char ch) { return std::isspace(ch); });
    }

    /**
     * Reads the IR file and returns the tuple block.
     * @param filename the IR file name.
     * */
    string readTuple(const string &filename) {
        string srch = "(tuple";
        string line;
        fstream file;
        file.open(filename, ios::in);

        if (file.is_open()) {
            while (getline(file, line)) {
                if (line.find(srch) != string::npos) {
                    return line;
                }
            }
        } else
            cout << "Couldn't access the file\n";
        return "";
    }

    auto fromString(std::string str) {
        std::vector<std::string> elements;

        std::regex r{R"([<\[" ]?([^<>\[\]" =\x0a\x0d]+)[>\[" ]?)"};
        std::istringstream iss(str);
        auto it = std::sregex_iterator(str.begin(), str.end(), r);
        auto end = std::sregex_iterator();
        for (; it != end; ++it) {
            auto match = *it;
            auto element = match[1].str().append(" ");
            elements.push_back(element);
        }
        return elements;
    }

    /**
     * Remove the parentheses from a string.
     * @param in the input string.
     * */
    string strip_parentheses(string in) {
        for (int i = 0; i < in.size(); i++) {
            if (in[0] == '(') {
                in = in.substr(1, in.size());
            }
        }
        for (int i = 0; i < in.size(); i++) {
            if (in[in.size() - 1] == ')') {
                in = in.substr(0, in.size() - 1);
            }
        }
        return in;
    }

    bool is_number(const string &s) {
        string::const_iterator it = s.begin();
        while (it != s.end() && isdigit(*it))
            ++it;
        return !s.empty() && it == s.end();
    }

    /**
     * Reads the IR file and returns the let block.
     * @param filename the IR file name.
     * */
    vector<string> readLet(string filename) {
        string srch = " (let";
        string line;
        fstream file;
        vector<string> res;
        int found = 0;
        string l;
        int brk;
        file.open(filename, ios::in);

        if (file.is_open()) {
            while (getline(file, line)) {
                if (line == srch) {
                    found = 1;
                }
                if (found) {
                    while (getline(file, l)) {
                        if (l.find("tuple") != string::npos) {
                            return res;
                        }
                        res.push_back(l);
                    }
                }
            }
        } else
            cout << "Couldn't access the file\n";
        return res;
    }

    /**
     * Parse the let block.
     * @param filename the IR file name.
     * */
    string parse_let(string filename) {
        /// A stack for parsing nested operations between parentheses.
        stack<string> st;
        /// A temp variable.
        string s;

        /// A string vector that contains the instructions included in the Let block of the IR.
        vector<string> vec = readLet(filename);

        /// If the vector is empty, then there is no Let block.
        if (vec.empty()) {
            return "";
        }
        /// The first element is "(", which is useless.
        vec.erase(vec.begin());
        /// The arithmetic circuit created as a result of parsing the Let block.
        string cir_print;
        /// A string vector that holds the instruction's operation and operands.
        vector<string> inst;
        /// A stack that stores the result of the last instruction that may be used in next operations.
        stack<string> pending;

        /// Process each line from the vector. Each line can include more than one instruction.
        for (auto line: vec) {
            s = line;
            /// Remove the spaces at the beginning and at the end of the instruction.
            boost::trim(s);

            /// This loop is for processing nested parentheses and extracting the inner most operation
            for (char const c: s) {
                if (c == '(') {
                    st.push(string(&c, 1));
                    continue;
                }
                if (st.empty())
                    break;
                st.top() += c;

                /// Once we encounter a ")", it means we got an instruction. Push the instruction into the isnt vector.
                if (c == ')') {
                    // cout << st.top() << endl;
                    inst.push_back(st.top());
                    st.pop();
                }
            }

            for (string line: inst) {
                /// Remove the parentheses from the instruction
                line = strip_parentheses(line);
                /// Remove extra spaces between the instruction's tokens.
                line = removeSpaces(line);
                // cout << line << endl;
                /// Get the instruction's tokens: operation, operand1, operand2
                auto tokens = split(line, ' ');
                /// How many tokens determines what we are going to parse
                size_t tokens_size = tokens.size();

                /// Get the operation
                if (tokens[0] == "bvmul") {
                    op = "*";
                } else if (tokens[0] == "bvadd") {
                    op = "+";
                } else if (tokens[0] == "bvsub") {
                    op = "-";
                }
                    /// This means that we are storing array variables into the vars_indx to be used during next operations.
                else if (tokens[0][0] == '#' && arr_flag) {
                    /// Get the array label (e.g., '0, '1, etc..)
                    string indx_lbl = removeSpaces(strip_parentheses(inst[inst.size() - 1]));
                    string tmp = indx_lbl;
                    /// Iterate over the array elements
                    for (int i = 0; i < tokens.size(); i++) {
                        /// Convert the binary string to integer
                        string val = tokens[i];
                        int int_val = stoi(val.substr(2, val.size()), nullptr, 2);
                        /// Set the value name to its array label appended with the value index.
                        /// for example, if the value is in array 1 and its index is 0, then the label is '1'0
                        indx_lbl += "\'" + to_string((i));
                        vars_indx[indx_lbl] = vars_cntr;
                        /// create the arithmetic circuit print, increment the counter, reset the indx_lbl to the array label.
                        cir_print += "$r" + to_string(vars_cntr) + " := " + to_string(int_val) + "\n";

                        string ele = "r" + to_string(vars_cntr);
                        eval_table[ele] = int_val;

                        vars_cntr++;
                        indx_lbl = tmp;
                    }
                    /// Now we are done with array, set the flag to false.
                    arr_flag = false;
                    break;
                }
                    /// It may not be an operation, rather an index to store a value or
                    /// a result of a computation
                else if (tokens[0][0] == '\'') {
                    res_indx_tmp = tokens[0];
                } else if (tokens[0] == "bv2pf") {

                    if (inst.size() ==
                        3) { /// In case we have ('0 ((bv2pf plapla) #b0101)), we are storing a value at an index
                        /// get the array index
                        string indx_val = strip_parentheses(inst[1]);
                        boost::trim(indx_val);
                        indx_lbl_arr_indx = removeSpaces(strip_parentheses(inst[2]));
                        arr_indx[indx_lbl_arr_indx] = stoi(indx_val.substr(2, indx_val.size()), nullptr, 2);
                        /// Skip the rest as the next token is a modulu number.
                        break;
                    } else if (inst.size() == 5 || inst.size() == 4) {
                        bool is_select = false;
                        for (auto stmt: inst) {
                            if (stmt.find("select") != string::npos) {
                                is_select = true;
                                break;
                            }
                        }
                        if (!is_select) {
                            indx_lbl_arr_indx = inst[inst.size() - 1];
                            indx_lbl_arr_indx = removeSpaces(strip_parentheses(indx_lbl_arr_indx));
                            next_is_indx = true;
                        }
                        continue;
                    } else {
                        cout << "Unknown instruction pattern!" << endl;
                        exit(5);
                    }
                } /// Useless for the current application
                else if (tokens[0] == "mod" || tokens[0] == "bv") {
                    continue;
                } /// Set the flag to indicate that the next step is to store the array elements.
                else if (tokens[0] == "array") {
                    arr_flag = true;
                    continue;
                }
                    /// This indicates an array access
                else if (tokens[0] == "select") {
                    if (tokens_size == 2) { /// It means that we will read array label from the tokens, but the value index is read from the eval_table.
                        /// because the index in this case is computed during previous instructions.
                        string top = pending.top();
                        top = top.substr(1, top.size());
                        pending.pop();
                        string val_indx = to_string(eval_table[top]);
                        string op1_lbl = tokens[1] + "\'" + val_indx;
                        op1_indx = vars_indx[op1_lbl];
                        op1_tmp = "$r" + to_string(op1_indx);
                        pending.push(op1_tmp);
                    } else {
                        if (is_op1) {
                            /// The label of operand is created by concatentaing its array label and its index within the array.
                            string op1_lbl = tokens[1] + "\'" + to_string(arr_indx[tokens[2]]);
                            if (vars_indx.find(op1_lbl) == vars_indx.end()) {
                                op1_lbl = store_array_lbl + "\'" + to_string(arr_indx[tokens[2]]);
                            }
                            is_op1 = false;
                            op1_indx = vars_indx[op1_lbl];
                            op1_tmp = "$r" + to_string(op1_indx);
                            pending.push(op1_tmp);
                            res_indx = op1_indx;
                        } else {
                            /// The label of operand is created by concatentaing its array label and its index within the array.
                            string op2_lbl = tokens[1] + "\'" + to_string(arr_indx[tokens[2]]);
                            if (vars_indx.find(op2_lbl) == vars_indx.end()) {
                                op2_lbl = store_array_lbl + "\'" + to_string(arr_indx[tokens[2]]);
                            }
                            is_op1 = true;
                            op2_indx = vars_indx[op2_lbl];
                            op2_tmp = "$r" + to_string(op2_indx);
                            /// Switch the order of the operands, so we pop the first operand then the second.
                            //string tmp_op1 = pending.top();
                            //pending.pop();
                            pending.push(op2_tmp);
                            //pending.push(tmp_op1);
                            res_indx = op2_indx;
                        }
                    }
                    continue;
                } else if (isStringEmptyOrWhitespace(tokens[0])) {
                    continue;
                } else if (tokens[0] == "store") {
                    string indx_lbl;
                    if (first_store_inst) { /// The firsr store instruction we encounter is the one that has the array label in which we store the result.
                        /// next store instructions points to an index that is not an array, but to an index in another array (which is the array
                        /// referenced by the first store instruction)

                        /// Toggle the flag
                        first_store_inst = false;
                        /// Ge the target array label in which we will store the result
                        store_array_lbl = tokens[1];
                        /// Get the index (in the target array) at which we store the result.
                        indx_lbl = store_array_lbl + "\'" + to_string(arr_indx[tokens[2]]);
                    } else {
                        /// Get the index (in the target array) at which we store the result.
                        indx_lbl = store_array_lbl + "\'" + to_string(arr_indx[tokens[2]]);
                    }
                    /// Get the last computation in the pending stack
                    string top = pending.top();
                    pending.pop();
                    /// retrive the index of the indx_lbl. (It must be registered in the vars_indx beforehand).
                    int store_indx = vars_indx[indx_lbl];
                    /// This is the left-side operand that we are modifying its value
                    string left = "r" + to_string(store_indx);
                    /// This is the new value to be assigned to the left-side.
                    string right = top.substr(1, top.size());

                    cir_print += "$" + left + " := " + right + "\n";

                    /// Re-assign the value in the eval_table
                    eval_table[left] = eval_table[right];

                    continue;
                } else {
                    cout << "Unknown token >> " << tokens[0] << endl;
                    exit(4);
                }
                /// If the instruction size is 3, then we have operator, operand 1, operand 2
                if (tokens_size == 3) {
                    /// Read operand 1
                    op1_tmp = tokens[1];
                    /// If it starts with #, then it is a constant value encoded in binary (e.g., #b010101).
                    if (op1_tmp[0] == '#') {
                        /// skip the first two chars (# and b) and convert the binary into integer.
                        op1 = stoi(op1_tmp.substr(2, op1_tmp.size()), nullptr, 2);
                        op1_indx = vars_cntr;
                        vars_cntr++;
                        cir_print += "$r" + to_string(op1_indx) + " := " + to_string(op1) + "\n";
                        string tmp = "r" + to_string(op1_indx);
                        eval_table[tmp] = op1;
                    }
                        /// If it starts with ' (single quotes), then it is an index to a value. Its index is retrieved
                        /// from the vars_indx map, or store it in the vars_indx map.
                    else if (op1_tmp[0] == '\'') {
                        /// iterate over the map to find the op1
                        it = vars_indx.find(op1_tmp);
                        /// If it is not stored in the map, then ...
                        if (it == vars_indx.end()) {
                            /// ... get its value, and ...
                            if (op1_tmp.size() > 2) {
                                op1_indx = stoi(op1_tmp.substr(2, op1_tmp.size())) + vars_cntr;
                            } else {
                                op1_indx = stoi(op1_tmp.substr(1, op1_tmp.size())) + vars_cntr;
                            }
                            /// ... store it in the map.
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                        } else {
                            /// If found, retrieve its index value
                            op1_indx = vars_indx[op1_tmp];
                        }
                    }
                        /// If op1_tmp is all chars, then it is a variable name.
                    else if (all_of(op1_tmp.begin(), op1_tmp.end(), [](char ch) { return isalpha(ch); })) {
                        /// Iterate over the vars_indx to retrieve its index.
                        it = vars_indx.find(op1_tmp);
                        /// If it is not found, then store it in the vars_indx map.
                        if (it == vars_indx.end()) {
                            op1_indx = vars_cntr;
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                            cir_print += "$r" + to_string(op1_indx) + " := " + op1_tmp + "\n";
                        } else { /// if it is found, retrieve its index.
                            op1_indx = vars_indx[op1_tmp];
                        }
                    } else {
                        cout << "Unknown operand1! >> " << op1_tmp << endl;
                        exit(3);
                    }

                    op2_tmp = tokens[2];
                    if (op2_tmp[0] == '#') {
                        op2 = stoi(op2_tmp.substr(2, op2_tmp.size()), nullptr, 2);
                        op2_indx = vars_cntr;
                        vars_cntr++;
                        cir_print += "$r" + to_string(op2_indx) + " := " + to_string(op2) + "\n";
                        string tmp = "r" + to_string(op2_indx);
                        eval_table[tmp] = op2;
                    } else if (op2_tmp[0] == '\'') {
                        it = vars_indx.find(op2_tmp);
                        if (it == vars_indx.end()) {
                            if (op2_tmp.size() > 2) {
                                op2_indx = stoi(op2_tmp.substr(2, op2_tmp.size())) + vars_cntr;
                            } else {
                                op2_indx = stoi(op2_tmp.substr(1, op2_tmp.size())) + vars_cntr;
                            }
                            vars_cntr++;
                            vars_indx[op2_tmp] = op2_indx;
                        } else {
                            op2_indx = vars_indx[op2_tmp];
                        }
                    } else if (all_of(op2_tmp.begin(), op2_tmp.end(), [](char ch) { return isalpha(ch); })) {
                        it = vars_indx.find(op2_tmp);
                        if (it == vars_indx.end()) {
                            op2_indx = vars_cntr;
                            vars_cntr++;
                            vars_indx[op2_tmp] = op2_indx;
                            cir_print += "$r" + to_string(op2_indx) + " := " + op2_tmp + "\n";
                        } else {
                            op2_indx = vars_indx[op2_tmp];
                        }
                    } else {
                        cout << "Unknown operand2! >> " << op2_tmp << endl;
                        exit(3);
                    }
                    res_indx = vars_cntr;
                    cir_print += "$r" + to_string(res_indx) + " := r" + to_string(op1_indx) + " " + op + " r" +
                                 to_string(op2_indx) + "\n";

                    string tmp1 = "r" + to_string(res_indx);
                    string tmp2 = "r" + to_string(op1_indx);
                    string tmp3 = "r" + to_string(op2_indx);

                    if (eval_table.find(tmp2) != eval_table.end()) {
                        if (eval_table.find(tmp3) != eval_table.end()) {
                            if (op == "+")
                                eval_table[tmp1] = eval_table[tmp2] + eval_table[tmp3];
                            else if (op == "*")
                                eval_table[tmp1] = eval_table[tmp2] * eval_table[tmp3];
                            else if (op == "-")
                                eval_table[tmp1] = eval_table[tmp2] - eval_table[tmp3];
                        } else {
                            cout << tmp3 << " (op2 --- Line 618) does not exist in eval_table" << endl;
                        }
                    } else {
                        cout << tmp2 << " (op1 --- Line 623) does not exist in eval_table" << endl;
                    }
                }
                    /// If the instruction size is 2, then we have operator, operand 1 only, operand 2 will be popped
                    /// from the pending stack
                else if (tokens_size == 2) {
                    /// read operand1
                    op1_tmp = tokens[1];
                    /// If it starts with #, then it is a constant value encoded in binary (e.g., #b010101).
                    if (op1_tmp[0] == '#') {
                        op1 = stoi(op1_tmp.substr(2, op1_tmp.size()), nullptr, 2);
                        op1_indx = vars_cntr;
                        vars_cntr++;
                        cir_print += "$r" + to_string(op1_indx) + " := " + to_string(op1) + "\n";
                        string tmp = "r" + to_string(op1_indx);
                        eval_table[tmp] = op1;
                    } else if (op1_tmp[0] == '\'') {
                        /// If it starts with ', it is an index
                        it = vars_indx.find(op1_tmp);
                        if (it == vars_indx.end()) {
                            if (op1_tmp.size() > 2) {
                                op1_indx = stoi(op1_tmp.substr(2, op1_tmp.size())) + vars_cntr;
                            } else {
                                op1_indx = stoi(op1_tmp.substr(1, op1_tmp.size())) + vars_cntr;
                            }
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                        } else {
                            op1_indx = vars_indx[op1_tmp];
                        }
                    } /// If it is all chars, then it is a variable
                    else if (all_of(op1_tmp.begin(), op1_tmp.end(), [](char ch) { return isalpha(ch); })) {
                        it = vars_indx.find(op1_tmp);
                        if (it == vars_indx.end()) {
                            op1_indx = vars_cntr;
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                            cir_print += "$r" + to_string(op1_indx) + " := " + op1_tmp + "\n";
                        } else {
                            op1_indx = vars_indx[op1_tmp];
                        }
                    } else {
                        cout << "Unknown operand1! >> " << op1_tmp << endl;
                        exit(3);
                    }
                    if (pending.empty()) {
                        break;
                    }
                    /// get the result of the previous operation from the pending stack.
                    /// This is considered operand2
                    string next = pending.top();
                    pending.pop();
                    /***This is part was errorouns!*/
                    /// read from the letter "r" until the ":" symbol
                    ///next = next.substr(1, next.find(":"));
                    /***END*/
                    //Trim the $ and r
                    next = next.substr(1, next.size());
                    res_indx = vars_cntr;
                    cir_print +=
                            "$r" + to_string(res_indx) + " := " + next + " " + op + " r" + to_string(op1_indx) + "\n";

                    string tmp1 = "r" + to_string(res_indx);
                    string tmp2 = next; //"r" + next;
                    string tmp3 = "r" + to_string(op1_indx);

                    if (eval_table.find(tmp2) != eval_table.end()) {
                        if (eval_table.find(tmp3) != eval_table.end()) {
                            if (op == "+")
                                eval_table[tmp1] = eval_table[tmp2] + eval_table[tmp3];
                            else if (op == "*")
                                eval_table[tmp1] = eval_table[tmp2] * eval_table[tmp3];
                            else if (op == "-")
                                eval_table[tmp1] = eval_table[tmp2] - eval_table[tmp3];
                        } else {
                            cout << tmp3 << " (op1 -- Line 715) does not exist in eval_table" << endl;
                        }
                    } else {
                        cout << tmp2 << " (op2 -- Line 720) does not exist in eval_table" << endl;
                    }
                } /// it is either an operation (bvadd, bvmul, bvsub) or a result index
                else if (tokens_size == 1) {
                    /// the operands are the top two elements in stack
                    string token = tokens[0];
                    if (token == "bvmul") {
                        if (pending.size() >= 2) {
                            op1_tmp = pending.top();
                            pending.pop();
                            op2_tmp = pending.top();
                            pending.pop();
                            res_indx = vars_cntr;
                            cir_print +=
                                    "$r" + to_string(res_indx) + " := " + op1_tmp.substr(1, op1_tmp.size()) + " * " +
                                    op2_tmp.substr(1, op2_tmp.size()) + "\n";

                            string tmp1 = "r" + to_string(res_indx);
                            string tmp2 = op1_tmp.substr(1, op1_tmp.size());
                            string tmp3 = op2_tmp.substr(1, op2_tmp.size());

                            if (eval_table.find(tmp2) != eval_table.end()) {
                                if (eval_table.find(tmp3) != eval_table.end()) {

                                    eval_table[tmp1] = eval_table[tmp2] * eval_table[tmp3];
                                } else {
                                    cout << tmp3 << " (op1 --- Line 751) does not exist in eval_table" << endl;
                                }
                            } else {
                                cout << tmp2 << " (op2 --- Line 756) does not exist in eval_table" << endl;
                            }
                        } else {
                            cout << "There isn't enough operands in the pending stack for bvmul!" << endl;
                        }
                    } else if (token == "bvadd") {
                        if (pending.size() >= 2) {
                            op1_tmp = pending.top();
                            pending.pop();
                            op2_tmp = pending.top();
                            pending.pop();
                            res_indx = vars_cntr;
                            cir_print +=
                                    "$r" + to_string(res_indx) + " := " + op1_tmp.substr(1, op1_tmp.size()) + " + " +
                                    op2_tmp.substr(1, op2_tmp.size()) + "\n";

                            string tmp1 = "r" + to_string(res_indx);
                            string tmp2 = op1_tmp.substr(1, op1_tmp.size());
                            string tmp3 = op2_tmp.substr(1, op2_tmp.size());

                            if (eval_table.find(tmp2) != eval_table.end()) {
                                if (eval_table.find(tmp3) != eval_table.end()) {

                                    eval_table[tmp1] = eval_table[tmp2] + eval_table[tmp3];
                                } else {
                                    cout << tmp3 << " (op2 -- Line 790) does not exist in eval_table" << endl;
                                }
                            } else {
                                cout << tmp2 << " (op1 -- Line 793) does not exist in eval_table" << endl;
                            }
                        } else {
                            cout << "There isn't enough operands in the pending stack for bvadd!" << endl;
                        }
                    } else if (token == "bvsub") {
                        if (pending.size() >= 2) {
                            op1_tmp = pending.top();
                            pending.pop();
                            op2_tmp = pending.top();
                            pending.pop();
                            res_indx = vars_cntr;
                            cir_print +=
                                    "$r" + to_string(res_indx) + " := " + op1_tmp.substr(1, op1_tmp.size()) + " - " +
                                    op2_tmp.substr(1, op2_tmp.size()) + "\n";

                            string tmp1 = "r" + to_string(res_indx);
                            string tmp2 = op1_tmp.substr(1, op1_tmp.size());
                            string tmp3 = op2_tmp.substr(1, op2_tmp.size());

                            if (eval_table.find(tmp2) != eval_table.end()) {
                                if (eval_table.find(tmp3) != eval_table.end()) {

                                    eval_table[tmp1] = eval_table[tmp2] - eval_table[tmp3];
                                } else {
                                    cout << tmp3 << " (op2 --- Line 827) does not exist in eval_table" << endl;
                                }
                            } else {
                                cout << tmp2 << " (op1 --- Line 830) does not exist in eval_table" << endl;
                            }
                        } else {
                            cout << "There isn't enough operands in the pending stack for bvsub!" << endl;
                        }
                    } else if (token[0] == '\'') {
                        vars_indx[token] = res_indx;
                        vars_cntr--;
                    }
                } else {
                    cout << "Skipping >> " << op1_tmp << endl;
                    continue;
                }
                /// push the current operation into the pending stack.
                string pen = "$r" + to_string(res_indx);
                pending.push(pen);
                vars_cntr++;

                if (next_is_indx) {
                    next_is_indx = false;
                    string name = "r" + to_string(res_indx);
                    arr_indx[indx_lbl_arr_indx] = eval_table[name];
                }
            }

            /// Clear the inst vector to get the next instruction.
            inst.clear();
        }
        return cir_print;
    }

    /**
     * Parse the tuple block.
     * @param filename the IR file name.
     * */
    string parse_tuple(const string &filename) {

        /// Reset op1 turn to parse the select operation.
        is_op1 = true;
        /// A stack for parsing the IR, given that the operations are organized in nested parentheses
        stack<string> st;
        /// Read the IR output and return the code which starts with "(tuple"
        string zok_ir = readTuple(filename);
        if (zok_ir[0] == ' ') {
            zok_ir.erase(0);
        }
        // cout << zok_ir << endl;
        /// convert the code into an equation
        string eqn = "";
        /// Transform the IR into a simpler form for creating and executing the circuit.
        string cir_print = "";
        /// If an instruction is missing an operand, it means that the second operand is the one resulting from the
        /// previous computation. The result of the previous computation is stored in this stack.
        stack<string> pending;
        /// Loop over the code and parse strip the parentheses
        for (char const c: zok_ir) {
            if (c == '(') { /// The start of an operation
                st.push(string(&c, 1));
                continue;
            }
            if (st.empty()) {
                break;
            }
            st.top() += c;

            if (c == ')') {
                bool is_select = false;
                /// The end of an operation
                /// get an instruction
                auto inst = st.top();
                /// remove the first and last parentheses
                inst = inst.substr(1, inst.size() - 2);
                /// remove additional spaces between each word
                inst = removeSpaces(inst);
                /// split the instructions into tokens: operation operand1 operand2 OR operation operand1
                auto tokens = split(inst, ' ');
                /// The first token is the operation
                string token = tokens[0];
                int tokens_size = tokens.size();
                if (token == "bvadd") {
                    op = "+";
                } else if (token == "bvmul") {
                    op = "*";
                } else if (token == "bvsub") {
                    op = "-";
                } else if (token == "tuple") {
                    break;
                } else if (token == "select") {
                    // *********************************************************** //
                    //                  continue;                                  //
                    // Earlier, we used to skip this operation.                    //
                    // But now we will parse it. NOTICE that it may cause errors   //
                    // for programs that had been parsed sucessfully               //
                    // *********************************************************** //
                    is_select = true;
                    if (tokens_size ==
                        2) { /// It means that we will read array label from the tokens, but the value index is read from the eval_table.
                        /// because the index in this case is computed during previous instructions.
                        string top = pending.top();
                        top = top.substr(1, top.size());
                        pending.pop();
                        string val_indx = to_string(eval_table[top]);
                        string op1_lbl = tokens[1] + "\'" + val_indx;
                        op1_indx = vars_indx[op1_lbl];
                        op1_tmp = "$r" + to_string(op1_indx);
                        pending.push(op1_tmp);
                    } else {
                        if (is_op1) {
                            /// The label of operand is created by concatentaing its array label and its index within the array.
                            string op1_lbl = tokens[1] + "\'" + to_string(arr_indx[tokens[2]]);
                            if (vars_indx.find(op1_lbl) == vars_indx.end()) {
                                op1_lbl = store_array_lbl + "\'" + to_string(arr_indx[tokens[2]]);
                            }
                            is_op1 = false;
                            op1_indx = vars_indx[op1_lbl];
                            op1_tmp = "$r" + to_string(op1_indx);
                            pending.push(op1_tmp);
                            res_indx = op1_indx;
                        } else {
                            /// The label of operand is created by concatentaing its array label and its index within the array.
                            string op2_lbl = tokens[1] + "\'" + to_string(arr_indx[tokens[2]]);
                            if (vars_indx.find(op2_lbl) == vars_indx.end()) {
                                op2_lbl = store_array_lbl + "\'" + to_string(arr_indx[tokens[2]]);
                            }
                            is_op1 = true;
                            op2_indx = vars_indx[op2_lbl];
                            op2_tmp = "$r" + to_string(op2_indx);
                            /// Switch the order of the operands, so we pop the first operand then the second.
                            string tmp_op1 = pending.top();
                            pending.pop();
                            pending.push(op2_tmp);
                            pending.push(tmp_op1);
                            res_indx = op2_indx;
                            st.pop();
                            st.pop();
                        }
                    }
                    continue;
                } else if (token == "=" || token == "not" || token == "ite") {
                    ite_flg = 1;
                } else {
                    cout << "Unknown operand >> " << token << endl;
                    exit(2);
                }
                /// if we have operation operand1 operand2
                if (tokens.size() == 3 && !ite_flg) {
                    op1_tmp = tokens[1]; /// get the first operand
                    op2_tmp = tokens[2]; /// get the second operand
                    if (op1_tmp[0] == '#') { /// if is starts with #, it means that is a value encoded in binary
                        /// convert the binary to integer then to string
                        op1 = stoi(op1_tmp.substr(2, op1_tmp.size()), nullptr, 2);
                        op1_indx = vars_cntr++;
                        cir_print += "$r" + to_string(op1_indx) + " := " + to_string(op1) + "\n";
                    } else if (op1_tmp[0] == '\'') {
                        it = vars_indx.find(op1_tmp);
                        if (it == vars_indx.end()) {
                            if (op1_tmp.size() > 2) {
                                op1_indx = stoi(op1_tmp.substr(2, op1_tmp.size())) + vars_cntr;
                            } else {
                                op1_indx = stoi(op1_tmp.substr(1, op1_tmp.size())) + vars_cntr;
                            }
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                        } else {
                            op1_indx = vars_indx[op1_tmp];
                        }
                    } else if (all_of(op1_tmp.begin(), op1_tmp.end(), [](char ch) { return isalpha(ch); })) {
                        it = vars_indx.find(op1_tmp);
                        if (it == vars_indx.end()) {
                            op1_indx = vars_cntr;
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                            cir_print += "$r" + to_string(op1_indx) + " := " + op1_tmp + "\n";
                        } else {
                            op1_indx = vars_indx[op1_tmp];
                        }
                    } else {
                        cout << "Unknown operand1 >> " << op1_tmp << endl;
                        exit(4);
                    }

                    if (op2_tmp[0] == '#') { /// if is starts with #, it means that is a value encoded in binary
                        /// convert the binary to integer then to string
                        op2 = stoi(op2_tmp.substr(2, op2_tmp.size()), nullptr, 2);
                        op2_indx = vars_cntr++;
                        cir_print += "$r" + to_string(op2_indx) + " := " + to_string(op2) + "\n";
                    } else if (op2_tmp[0] == '\'') {
                        it = vars_indx.find(op2_tmp);
                        if (it == vars_indx.end()) {
                            if (op2_tmp.size() > 2) {
                                op2_indx = stoi(op2_tmp.substr(2, op2_tmp.size())) + vars_cntr;
                            } else {
                                op2_indx = stoi(op2_tmp.substr(1, op2_tmp.size())) + vars_cntr;
                            }
                            vars_cntr++;
                            vars_indx[op2_tmp] = op2_indx;
                        } else {
                            op2_indx = vars_indx[op2_tmp];
                        }
                    } else if (all_of(op2_tmp.begin(), op2_tmp.end(), [](char ch) { return isalpha(ch); })) {
                        it = vars_indx.find(op2_tmp);
                        if (it == vars_indx.end()) {
                            op2_indx = vars_cntr;
                            vars_cntr++;
                            vars_indx[op2_tmp] = op2_indx;
                            cir_print += "$r" + to_string(op2_indx) + " := " + op2_tmp + "\n";
                        } else {
                            op2_indx = vars_indx[op2_tmp];
                        }
                    } else {
                        cout << "Unknown operand2 >> " << op2_tmp << endl;
                        exit(5);
                    }

                    /// append the operation into the equation
                    eqn += op1;
                    eqn += op;
                    eqn += op2;

                    /// append the operation to the circuit description
                    cir_print += "$r" + to_string(vars_cntr) + " := r" + to_string(op1_indx) + " " + op +
                                 " r" + to_string(op2_indx) + "\n";
                }
                    /// Otherwise if we have operation operand1, we get the second operand from the stack.
                else if (tokens.size() == 2) {
                    /// read operand1
                    string op1_tmp = tokens[1];
                    if (op1_tmp[0] == '#') { /// if is starts with #, it means that is a value encoded in binary
                        /// convert the binary to integer then to string
                        op1 = stoi(op1_tmp.substr(2, op1_tmp.size()), nullptr, 2);
                        op1_indx = vars_cntr;
                        vars_cntr++;
                        cir_print += "$r" + to_string(op1_indx) + " := " + to_string(op1) + "\n";
                    } /// If it starts with ', then it is an index.
                    else if (op1_tmp[0] == '\'') {
                        /// Iterate over the vars_indx to get op1 index
                        it = vars_indx.find(op1_tmp);
                        /// If it is not found, set its index and store it in vars_indx.
                        if (it == vars_indx.end()) {
                            if (op1_tmp.size() > 2) {
                                op1_indx = stoi(op1_tmp.substr(2, op1_tmp.size())) + vars_cntr;
                            } else {
                                op1_indx = stoi(op1_tmp.substr(1, op1_tmp.size())) + vars_cntr;
                            }
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                        } else {
                            /// If it is found, the retrieve its index.
                            op1_indx = vars_indx[op1_tmp];
                        }
                        /// If op1_tmp is all chars, then it is a variable name.
                    } else if (all_of(op1_tmp.begin(), op1_tmp.end(), [](char ch) { return isalpha(ch); })) {
                        /// Iterate over the vars_indx map, if not found, set its index and store it in the vars_indx.
                        it = vars_indx.find(op1_tmp);
                        if (it == vars_indx.end()) {
                            op1_indx = vars_cntr;
                            vars_cntr++;
                            vars_indx[op1_tmp] = op1_indx;
                            cir_print += "$r" + to_string(op1_indx) + " := " + op1_tmp + "\n";
                        } else { /// if found, retrieve its index
                            op1_indx = vars_indx[op1_tmp];
                        }
                    } else {
                        cout << "Unkown operand1! >> " << op1_tmp << endl;
                        exit(3);
                    }
                    eqn += op;
                    eqn += op1;
                    if (pending.empty()) {
                        break;
                    }
                    /// get the result of the previous operation from the pending stack.
                    string next = pending.top();
                    pending.pop();
                    /// read from the letter "r" until the ":" symbol
                    next = next.substr(1, next.find(":"));
                    cir_print +=
                            "$r" + to_string(vars_cntr) + " := " + next + " " + op + " r" + to_string(op1_indx) + "\n";
                } else if (tokens.size() == 1 || ite_flg) {
                    /// it is either an operation (bvadd, bvmul, bvsub) or a result index
                    string token = tokens[0];
                    if (token == "bvmul") {
                        if (pending.size() >= 2) {
                            op1_tmp = pending.top();
                            pending.pop();
                            op2_tmp = pending.top();
                            pending.pop();
                            res_indx = vars_cntr;
                            cir_print +=
                                    "$r" + to_string(res_indx) + " := " + op1_tmp.substr(1, op1_tmp.size()) + " * " +
                                    op2_tmp.substr(1, op2_tmp.size()) + "\n";
                        } else {
                            cout << "There isn't enough operands in the pending stack for bvmul!" << endl;
                        }
                    } else if (token == "bvadd") {
                        if (pending.size() >= 2) {
                            op1_tmp = pending.top();
                            pending.pop();
                            op2_tmp = pending.top();
                            pending.pop();
                            res_indx = vars_cntr;
                            cir_print +=
                                    "$r" + to_string(res_indx) + " := " + op1_tmp.substr(1, op1_tmp.size()) + " + " +
                                    op2_tmp.substr(1, op2_tmp.size()) + "\n";
                        } else {
                            cout << "There isn't enough operands in the pending stack for bvadd!" << endl;
                        }
                    } else if (token == "bvsub") {
                        if (pending.size() >= 2) {
                            op1_tmp = pending.top();
                            pending.pop();
                            op2_tmp = pending.top();
                            pending.pop();
                            res_indx = vars_cntr;
                            cir_print +=
                                    "$r" + to_string(res_indx) + " := " + op1_tmp.substr(1, op1_tmp.size()) + " - " +
                                    op2_tmp.substr(1, op2_tmp.size()) + "\n";
                        } else {
                            cout << "There isn't enough operands in the pending stack for bvsub!" << endl;
                        }
                    } else if (token == "=") {
                        assert("There isn't enough operands in the pending stack for \"=\"!" && pending.size() >= 2);
                        op1_tmp = pending.top().substr(1, op1_tmp.size());
                        pending.pop();
                        op2_tmp = pending.top().substr(1, op2_tmp.size());
                        pending.pop();
                        string res_indx = "r" + to_string(vars_cntr);
                        eval_table[res_indx] = eval_table[op1_tmp] - eval_table[op2_tmp];
                        cir_print += "$" + res_indx + " := " + op1_tmp + " - " + op2_tmp + "\n";
                        vars_cntr++;

                        string tmp = "r" + to_string(vars_cntr);
                        cir_print += "$" + tmp + " := 1\n";
                        vars_cntr++;

                        /// Assume that the ptxt mod is a fixed value, 13;
                        int exp = ptxt_mod - 1;
                        string nxt_res_indx;
                        string base_indx = res_indx;

                        while (exp > 0) {
                            nxt_res_indx = "r" + to_string(vars_cntr);
                            if (exp % 2 != 0) {
                                cir_print += "$" + nxt_res_indx + " := " + tmp + " * " + base_indx + "\n";
                                /// skip adding it to the eval_table
                                tmp = nxt_res_indx;
                                vars_cntr++;
                                nxt_res_indx = "r" + to_string(vars_cntr);
                            }

                            cir_print += "$" + nxt_res_indx + " := " + base_indx + " * " + base_indx + "\n";
                            /// skip adding it to the eval_table
                            base_indx = nxt_res_indx;
                            vars_cntr++;
                            exp /= 2;
                        }

                        string exp_res = "r" + to_string(vars_cntr);
                        cir_print += "$" + exp_res + " := " + tmp + "\n";
                        // eval_table[res_indx] = -1; // Just a random value ...
                        ite_flg = 0;
                    } else if (token == "not") {
                        assert("There isn't enough operands in the pending stack for not!" && pending.size() >= 1);
                        op1_tmp = pending.top();
                        op1_tmp = op1_tmp.substr(1, op1_tmp.size());
                        pending.pop();
                        res_indx_tmp = "r" + to_string(vars_cntr);
                        eval_table[res_indx_tmp] = 1 - eval_table[op1_tmp];
                        cir_print += "$" + res_indx_tmp + " := 1\n";
                        vars_cntr++;

                        string tmp = res_indx_tmp;

                        res_indx_tmp = "r" + to_string(vars_cntr);
                        cir_print += "$" + res_indx_tmp + " := " + tmp + " - " + op1_tmp + "\n";
                        ite_flg = 0;
                    } else if (token == "ite") {
                        /**
                         * cond is computed by Fermat's little theorem, gives encrypted zero (equal) or encrypted one (unequal).
                         *      see -> https://github.com/microsoft/SEAL/issues/162
                         * if(cond):
                         *      res = 2
                         * else:             =====>  res = cond? 2:3   =====>  res = cond*2+(1-cond)*3
                         *      res = 3
                         * BUT BECAUSE WE GET 0 IF THE TWO VALUES ARE EQUAL AND 1 OTHERWISE, WE SWAP THE OPERANDS OF THE EQUATION
                         *                                             =====>  res = (1-cond)*2+cond*3
                         * */
                        assert("There isn't enough operands in the pending stack for ite!" && pending.size() >= 1);
                        string cond = pending.top();
                        cond = cond.substr(1, cond.size());
                        pending.pop();

                        op1_tmp = tokens[1]; /// get the first operand
                        op2_tmp = tokens[2]; /// get the second operand
                        if (op1_tmp[0] == '#') { /// if is starts with #, it means that is a value encoded in binary
                            /// convert the binary to integer then to string
                            op1 = stoi(op1_tmp.substr(2, op1_tmp.size()), nullptr, 2);
                            op1_indx = vars_cntr++;
                            cir_print += "$r" + to_string(op1_indx) + " := " + to_string(op1) + "\n";
                        } else if (op1_tmp[0] == '\'') {
                            it = vars_indx.find(op1_tmp);
                            if (it == vars_indx.end()) {
                                if (op1_tmp.size() > 2) {
                                    op1_indx = stoi(op1_tmp.substr(2, op1_tmp.size())) + vars_cntr;
                                } else {
                                    op1_indx = stoi(op1_tmp.substr(1, op1_tmp.size())) + vars_cntr;
                                }
                                vars_cntr++;
                                vars_indx[op1_tmp] = op1_indx;
                            } else {
                                op1_indx = vars_indx[op1_tmp];
                            }
                        } else if (all_of(op1_tmp.begin(), op1_tmp.end(), [](char ch) { return isalpha(ch); })) {
                            it = vars_indx.find(op1_tmp);
                            if (it == vars_indx.end()) {
                                op1_indx = vars_cntr;
                                vars_cntr++;
                                vars_indx[op1_tmp] = op1_indx;
                                cir_print += "$r" + to_string(op1_indx) + " := " + op1_tmp + "\n";
                            } else {
                                op1_indx = vars_indx[op1_tmp];
                            }
                        } else {
                            cout << "Unknown operand1 >> " << op1_tmp << endl;
                            exit(4);
                        }

                        if (op2_tmp[0] == '#') { /// if is starts with #, it means that is a value encoded in binary
                            /// convert the binary to integer then to string
                            op2 = stoi(op2_tmp.substr(2, op2_tmp.size()), nullptr, 2);
                            op2_indx = vars_cntr++;
                            cir_print += "$r" + to_string(op2_indx) + " := " + to_string(op2) + "\n";
                        } else if (op2_tmp[0] == '\'') {
                            it = vars_indx.find(op2_tmp);
                            if (it == vars_indx.end()) {
                                if (op2_tmp.size() > 2) {
                                    op2_indx = stoi(op2_tmp.substr(2, op2_tmp.size())) + vars_cntr;
                                } else {
                                    op2_indx = stoi(op2_tmp.substr(1, op2_tmp.size())) + vars_cntr;
                                }
                                vars_cntr++;
                                vars_indx[op2_tmp] = op2_indx;
                            } else {
                                op2_indx = vars_indx[op2_tmp];
                            }
                        } else if (all_of(op2_tmp.begin(), op2_tmp.end(), [](char ch) { return isalpha(ch); })) {
                            it = vars_indx.find(op2_tmp);
                            if (it == vars_indx.end()) {
                                op2_indx = vars_cntr;
                                vars_cntr++;
                                vars_indx[op2_tmp] = op2_indx;
                                cir_print += "$r" + to_string(op2_indx) + " := " + op2_tmp + "\n";
                            } else {
                                op2_indx = vars_indx[op2_tmp];
                            }
                        } else {
                            cout << "Unknown operand2 >> " << op2_tmp << endl;
                            exit(5);
                        }

                        res_indx_tmp = "r" + to_string(vars_cntr);
                        cir_print += "$" + res_indx_tmp + " := 1\n";
                        vars_cntr++;
                        string tmp = res_indx_tmp;

                        string one_mins_cond = "r" + to_string(vars_cntr);
                        eval_table[one_mins_cond] = 1 - eval_table[cond];
                        cir_print += "$" + one_mins_cond + " := " + tmp + " - " + cond + "\n";
                        vars_cntr++;

                        string iftrue = "r" + to_string(vars_cntr);
                        eval_table[iftrue] = eval_table[one_mins_cond] * op1;
                        cir_print += "$" + iftrue + " := " + one_mins_cond + " * r" + to_string(op1_indx) + "\n";
                        vars_cntr++;

                        string iffalse = "r" + to_string(vars_cntr);
                        eval_table[iffalse] = eval_table[cond] * op2;
                        cir_print += "$" + iffalse + " := " + cond + " * r" + to_string(op2_indx) + "\n";
                        vars_cntr++;

                        string res = "r" + to_string(vars_cntr);
                        eval_table[res] = eval_table[iffalse] + eval_table[iftrue];
                        cir_print += "$" + res + " := " + iftrue + " + " + iffalse + "\n";

                        ite_flg = 0;
                    } else {
                        cout << "Unknown operation >> " << token << endl;
                    }
                }
                /// push the current operation into the pending stack.
                string pen = "$r" + to_string(vars_cntr);
                pending.push(pen);
                vars_cntr++;
                st.pop();
            }
        }

        return cir_print;
    }

    string removeSpaces(string str_in) {
        string str = str_in;
        // Iterate over the string, and remove any double spaces.
        for (int i = 0; i < str.length(); i++) {
            if (str[i] == ' ' && str[i + 1] == ' ') {
                str.erase(i, 1);
            }
        }
        boost::trim(str);

        return str;
    }

public:
    Parser() {
        vars_cntr = 2;
        res_cntr = 2;
        op = "";
        op1 = -1;
        op1_indx = -1;
        op1_tmp = "";
        op2 = -1;
        op2_indx = -1;
        op2_tmp = "";
        res_indx_tmp = "-1";
        res_indx = -1;
    }

    string parse(const string &filename) {
        string parsed_let = parse_let(filename);
        string parsed_ir = parse_tuple(filename);
        string arith_cir = parsed_let.append(parsed_ir);
        return arith_cir;
    }
};

void export_opl(string cir, const string &filename) {
    ofstream out(filename);
    out << cir;
    out.close();
}

void export_python(const string &cir_print, const string &filename) {
    string pycode = cir_print;
    pycode.erase(remove(pycode.begin(), pycode.end(), '$'), pycode.end());
    pycode.erase(remove(pycode.begin(), pycode.end(), ':'), pycode.end());

    auto last_line = split(pycode, '\n');
    string var = last_line[last_line.size() - 2];
    var = var.substr(0, var.find(" "));

    pycode += "print(" + var + ") \n";

    string name = filename + ".py";
    ofstream out(name);
    out << pycode;
    out.close();
}

char *getCmdOption(char **begin, char **end, const std::string &option) {
    char **itr = std::find(begin, end, option);
    if (itr != end && ++itr != end) {
        return *itr;
    }
    return 0;
}

bool cmdOptionExists(char **begin, char **end, const std::string &option) {
    return std::find(begin, end, option) != end;
}

int main(int argc, char *argv[]) {
    string file = argv[1];
    Parser p;
    string parsed_ir = p.parse(file);
    cout << parsed_ir << endl;
    string outfile = file.substr(0, file.find('.'));
    string opl = outfile + ".opl";
    export_opl(parsed_ir, opl);
    export_python(parsed_ir, outfile);
    cout << "-------------------------" << endl;
    istringstream cir(parsed_ir);

    string inst;
    /// inst: result_indx := operand1 op operand2
    while (getline(cir, inst)) {
        auto vec = split(inst, ' ');
        string res_indx = vec[0].substr(2);
        if (vec.size() == 5) {
            string op1_indx = vec[2].substr(1);;
            string op = vec[3];
            string op2_indx = vec[4].substr(1);;

            if (op == "*") {
                cout << "mul(" << op1_indx << ", " << op2_indx << ", " << res_indx << ")\n";
            } else if (op == "+") {
                cout << "add(" << op1_indx << ", " << op2_indx << ", "
                     << "ONE_INDX, " << res_indx << ")\n";
            } else if (op == "-") {
                cout << "subtract(" << op1_indx << ", " << op2_indx << ", "
                     << "ONE_INDX, " << res_indx << ")\n";
            } else {
                cout << "Unknown operation!" << endl;
            }
        } else if (vec.size() == 3) { /// This is either a variable or a constant declaration
            string op1 = vec[2];
            if (is_number(op1)) { /// define a constant
                cout << "def_const(" << op1 << ", " << res_indx << ", "
                     << "ctxt, circuit.getHeEncoder(), *initializer.getEncryptor()\n";
            } else if (op1[0] == 'r') { /// Assignment to another variable
                cout << "assign(" << res_indx << ", " << op1.substr(1) << ")\n";
            } else {
                cout << "def_var(" << op1[0] << ", " << res_indx << ")\n";
            }
        }
    }

    char x;
    cin >> x;
}