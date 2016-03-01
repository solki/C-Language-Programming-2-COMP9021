/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * Description: This program will read two kinds of data from two files: names *
 *              and predicates. It will read a formal expression from standard *
 *              input and check whether that expression is syntactically       *
 *              correct, i.e., built from the names and predicates that have   *
 *              been read, together with a few boolean operators. Then your    *
 *              program will read from a third file a set of basic facts       *
 *              assumed to be true, and check whether the formal expression    *
 *              itself is true. Finally, it will find out whether it is        *
 *              possible to make some basic facts true to make the formal      *
 *              expression itself true (this being trivially the case if the   *
 *              answer to the previous question is positive), and in case it   *
 *              is, write a possible solution to a file. The program will use  *
 *              an abstract interface that you will have to implement. The     *
 *              interface and the client program will be provided.             *
 * Written by Zhang Xi (3472528) for COMP9021                                  *
 *                                                                             *
 * Other source files, if any, one per line, starting on the next line:        *
 *              reason.c                                                       *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include <stdbool.h>
#include <math.h>
#include "logic.h"

/*This structure is used for contain inputed formula as a binary tree in the memory.*/
typedef struct formula {
    int arity;
    char word[100];
    struct formula *subf1, *subf2;
}Form;
/*This link list is used to contain the contents of 'true_atoms.txt'.*/
typedef struct interpretation {
    char *words;
    struct interpretation *next_interp;
}Interp;
/*This structure is used to contain the contents of 'predicates.txt'.*/
typedef struct predic {
    char *predicates;
    int arity;
} Predicate;
Formula make_tree(Formula); //This function is used to recursively make a tree of inputted formula.
bool compare_atoms(char []); //This function is used to check if the atoms of input formula are exist in 'predicates.txt' and 'names.txt' by folowing the arity rule. 
bool logic_compare(char [], Interpretation intp); //This function is used to check if the atoms of inputted formula exist in the 'true_atoms.txt'.
void get_unit(Formula f); //This function is used to put atoms from form into the **unit.
void print_witness(Interpretation intp, int); //This function is used to finally print the minimal interpretations to file.
static int candidates = 0; //This variable is used to count the number of candidate minimal interpretations.
static int count_names = 0; //This variable is used to count the number of names from 'names.txt'.
static int count_predicates = 0; //This variable is used to count the number of predicates from 'predicates.txt'.
static int count_interp = 0; //This variable is used to count the number of interpretations from 'true_atom.txt'.also be used to count witnesses later.
static int count_brace = 0; //This variable is used to count the number of bracket, if it's '[' then ++count, whereas ']', then --count. the result should be 0.
static char ** names; //This pointer to pointer is used to contain data from 'names.txt'.
static char ** unit; //This pointer to pointer is used to contain atoms from form. Therefore I can get atoms easily from here.
bool conti = true; // This boolean variable is used to give a signal when EOF appears in the sub-function.
bool is_formula = true; //This boolean variable is used to give a signal whether or not to change the pointer to form into  NULL. 
Predicate *predicate; //This pointer is used to point to the location of predicates read from 'predicates.txt'.

void get_constants(FILE *fp) {
    int start = 0; //This variable is used to identify whether or not the nospace character come in. '1' refers to start name, '0' refers to space.
    int j = 0;
    int ch;
    names = malloc(sizeof(char *));
    while ((ch = getc(fp)) != EOF) {
        if (!isspace(ch)) {
            start = 1;
            names[count_names] = realloc(names[count_names], (j + 1) * sizeof(char));
            names[count_names][j++] = ch;
        }
        else if (isspace(ch) && start) {
            start = 0;
            names[count_names] = realloc(names[count_names], (j + 1) * sizeof(char));
            names[count_names][j] = '\0'; //add a '\0' at the end of each name
            j = 0;
            count_names++;
            names = realloc(names, (count_names + 1) * sizeof(char *));
        }
    }
}
void get_predicates(FILE *fp) {
    int ch = getc(fp);
    int j = 0;
    predicate = malloc(sizeof(Predicate));
    while (ch != EOF) {
        if (!j) {
            if (isspace(ch)) {
                ch = getc(fp);
                continue;
            }
            else {
                predicate[count_predicates].predicates = malloc(sizeof(char));
                predicate[count_predicates].predicates[j++] = ch;
                ch = getc(fp);
            }
        }
        else if (ch != '/') {
            predicate[count_predicates].predicates = realloc(predicate[count_predicates].predicates, (j + 1) * sizeof(char));
            predicate[count_predicates].predicates[j++] = ch;
            ch = getc(fp);
        }
        else {
            predicate[count_predicates].arity = 0;
            while (isdigit(ch = getc(fp)))
                predicate[count_predicates].arity = predicate[count_predicates].arity * 10 + ch - '0';
            predicate[count_predicates].predicates = realloc(predicate[count_predicates].predicates, (j + 1) * sizeof(char));
            predicate[count_predicates].predicates[j] = '\0'; //add a '\0' at the end of each predicate
            j = 0;
            count_predicates++;
            predicate = realloc(predicate, (count_predicates + 1) * sizeof(Predicate));
        }
    }
}
Formula make_formula() {
    int ch;
    int i = 0;
    int start = 0;
    int num_of_tree = 0;//Only one tree is accepted at the end. If not so, NULL will be returned.
    bool is_end = false; //When it reaches the end of formula in this function, this boolean variable will be set true.
    Formula fml = malloc(sizeof(Form));
    fml->arity = 0;
    fml->word[0] = '\0';
    while ((ch = getchar()) != EOF) {
        if (is_end && !isspace(ch)) {
            fml = NULL;
            continue;
        }
        if (isspace(ch) && !start && fml)
            continue;
        else if (ch == ']' && fml && !start) {
            count_brace--;
            continue;
        }
        else if (isspace(ch) && start && fml) {
            start = 0;
            fml->word[i] = '\0'; //add a '\0' at the end of each word
            if (strcmp(fml->word, "not")
                && strcmp(fml->word, "and")
                && strcmp(fml->word, "or")
                && strcmp(fml->word, "iff")
                && strcmp(fml->word, "implies")) {
                fml->arity = 0;
                fml->subf1 = NULL;
                fml->subf2 = NULL;
                num_of_tree++;
                is_end = true;
            }
            else if (!strcmp(fml->word, "not") && ch != ']') {
                fml->arity = 1;
                fml->subf2 = NULL;
                fml->subf1 = malloc(sizeof(Form));
                fml->subf1 = make_tree(fml->subf1);
                num_of_tree++;
            }
            else if ((!strcmp(fml->word, "and")
                      || !strcmp(fml->word, "or")
                      || !strcmp(fml->word, "iff")
                      || !strcmp(fml->word, "implies"))
                     && ch != ']') {
                fml->arity = 2;
                fml->subf2 = malloc(sizeof(Form));
                fml->subf2 = make_tree(fml->subf2);
            }
            else if ((!strcmp(fml->word, "not")
                      || !strcmp(fml->word, "and")
                      || !strcmp(fml->word, "or")
                      || !strcmp(fml->word, "iff")
                      || !strcmp(fml->word, "implies"))
                     && ch == ']')
                is_formula = false;
        }
        
        else if (ch == '[' && !start && fml) {
            count_brace++;
            fml->subf1 = malloc(sizeof(Form));
            fml->subf1 = make_tree(fml->subf1);
            num_of_tree++;
            fml->arity = 2;
        }
        else if ((((!isalpha(ch) && !isspace(ch) && ch != '_') && !start)
             || (!(isalpha(ch)) && ch != '_' && !isdigit(ch) && ch != ',' && ch != '(' && ch != ')' && start)) && fml) {
            fml = NULL;
            continue;
        }
        else if ((((isalpha(ch) || ch == '_') && !start)
                  || (((isdigit(ch) || isalpha(ch) || ch == '_' || ch == ',' || ch == '(' ||ch == ')') && start))) && fml) {
            if (!start)
                start = 1;
            fml->word[i++] = ch;
        }
        if (!conti) //this variable allocated here in each loop is used to check if the program got an EOF at sub function. if so jump out the loop. 
            break;
    }
    if (fml && (count_brace || !fml->word[0] || !is_formula || num_of_tree != 1))
        fml = NULL;
    return fml;
}
/*Here a recursive son-function is created to handle the part inside the "[]" or after operators. 'f' is the address of 'form' and 'left_or_right' indicates if it's
 * a element of atoms, or a sigle atom, at the left side of an boolean oprator or right side.*/
Formula make_tree(Formula f) {
    int i = 0;
    int sta = 0; //Same function as start, but different name here
    int c; //same as 'ch'
    f->arity = 0;
    f->word[0] = '\0';
    while ((c = getchar()) != EOF) {
        if (c == '[') {
            count_brace++;
            f->arity = 2;
            f->subf1 = malloc(sizeof(Form));
            f->subf1 = make_tree(f->subf1);
            if (!conti)
                break;
            else
                continue;
        }
        else if ((isspace(c) || c == ']') && sta) {
            if (c == ']')
                count_brace--;
            sta = 0;
            f->word[i] = '\0';//add a '\0' at the end of each word
            i = 0;
            if (strcmp(f->word, "not")
                && strcmp(f->word, "and")
                && strcmp(f->word, "or")
                && strcmp(f->word, "iff")
                && strcmp(f->word, "implies")) {
                f->arity = 0;
                f->subf1 = NULL;
                f->subf2 = NULL;
            }
            else if (!strcmp(f->word, "not")) {
                f->arity = 1;
                f->subf2 = NULL;
                f->subf1 = malloc(sizeof(Form));
                f->subf1 = make_tree(f->subf1);
            }
            else if (!strcmp(f->word, "and")
                     || !strcmp(f->word, "or")
                     || !strcmp(f->word, "iff")
                     || !strcmp(f->word, "implies")) {
                f->arity = 2;
                f->subf2 = malloc(sizeof(Form));
                f->subf2 = make_tree(f->subf2);
            }
            break;
        }
        else if (c == ']' && !sta) {
            count_brace--;
        }
        else if (!isspace(c) && !sta) {
            sta = 1;
            if (i)
                is_formula = false;
            f->word[i++] = c;
        }
        else if (!isspace(c) && sta)
            f->word[i++] = c;
    }
    /*When input reaches the end inside the recursive function, it will be also terminated in the upper layer by receiving this signal as false.*/
    if (c == EOF)
        conti = false;
    if (!is_formula)
        f = NULL;
    return f;
}
bool is_syntactically_correct(Formula f) {
    if (!f)
        return false;
    /*If it a leaf node, it should be null on both its subf1 pointers, then compare the data on the leaf with the predicates and names. If it's not then move on.*/
    if (!f->subf1 && !f->subf2) {
        if (f->word[0] == '\0')
            return false;
        else
            return compare_atoms(f->word);
    }
    /*if the arity of form is 2,it must be an operator except 'not'.*/
    else if (f->arity == 2) {
        if (strcmp(f->word, "and") && strcmp(f->word, "or") && strcmp(f->word, "iff") && strcmp(f->word, "implies"))
            return false;
        else if (!f->subf1 || !f->subf2)
            return false;
        else
            return is_syntactically_correct(f->subf1) && is_syntactically_correct(f->subf2); //The result of this operator node true or false depends on both the two returned result to this node. Both of them must be true, which makes this node true, otherwise, faulse.
    }
    /*if the arity of form is 1,it must be an operator 'not'.*/
    else {
        if (strcmp(f->word, "not"))
            return false;
        else if (!f->subf1 || f->subf2)
            return false;
        else
            return is_syntactically_correct(f->subf1); //The result of this operator node true or false depends on only one returned result to this node.
    }
}
bool compare_atoms(char origin[]) {
    char *input_prd; //used to contain the predicate part of one atom of inputted formula.
    char **name_input; //used to contain the name part of one atom of inputted formula one by one.
    int i0 = 0, i1 = 0, j1 = 0, k = 0; //These are different indexes. 
    int num_of_r_brace = 0; //Here I count the number of ')' it must be one at the end, otherwise return false.
    int tmp_ari = 0; //used to temperarily contain number of names counted from the arity of standard 'predicates.txt', when it fixes the number of names of inputted atom.
    int fit_names = 0; //used to contain the number of names from atoms fixed to standard 'names.txt'.
    bool is_name = false; //used to give a signal that predicateis end here comes the name part.
    bool is_predicate = false; //used to give a signal that the atom is fit to the predicate in the standard 'predicates.txt', also the number of names are the same. 
    while (origin[i0] != '\0') {
        if (num_of_r_brace)
            return false;
        if (origin[i0] != '(' && !is_name) {
            if (!i1)
                input_prd = malloc(sizeof(char));
            else
                input_prd = realloc(input_prd, (i1 + 1) * sizeof(char));
            input_prd[i1++] = origin[i0++];
        }
        else if (origin[i0] == '(' && !is_name) {
            is_name = true;
            i0++;
            input_prd[i1] = '\0'; //add a '\0' at the end of each predicate.
            name_input = malloc(sizeof(char *));
            name_input[j1] = malloc(sizeof(char));
        }
        else {
            if (origin[i0] == ',') {
                name_input[j1++][k] = '\0'; //add a '\0' at the end of each name.
                name_input = realloc(name_input, (j1 + 1) * sizeof(char *));
                name_input[j1] = malloc(sizeof(char));
                k = 0;
            }
            else if (origin[i0] == ')') {
                name_input[j1++][k] = '\0'; //add a '\0' at the end of each name.
                num_of_r_brace++;
                is_name = false;
            }
            else {
                name_input[j1] = realloc(name_input[j1], (k + 1) * sizeof(char));
                name_input[j1][k++] = origin[i0];
            }
            i0++;
        }
    }
    if (!j1) {
        input_prd = realloc(input_prd, (i1 + 1) * sizeof(char));
        input_prd[i1] = '\0';
    }
    /*This part is used to check if the atom is fit to the predicate in the standard 'predicates.txt', also the number of names are the same.*/
    if (is_name)
        return false;
    for (int j = 0; j < count_predicates; ++j) {
        if (!strcmp(predicate[j].predicates, input_prd) && predicate[j].arity == j1) {
            is_predicate = true;
            tmp_ari = predicate[j].arity;
            break;
        }
    }
    /*This part is used to check if the atom's name are truely exist in the 'names.txt'.*/
    if (!is_predicate)
        return false;
    for (int i = 0; i < j1; ++i)
        for (int j = 0; j < count_names; ++j) {
            if (!strcmp(names[j], name_input[i]))
                fit_names++;
        }
    if (fit_names < tmp_ari) //notice that the name contianed in the 'names.txt' may be repeated. so I use '<' instead of '!='.
        return false;
    else
        return true;
}
Interpretation make_interpretation(FILE *fp) {
    int ch;
    int start = 0, i = 0;
    Interpretation intp = malloc(sizeof(Interp)); //This is initialized as the pointer to the address of interpretation, but it will be modifyed in the programming. 
    Interpretation intp2 = intp; //thus, I use another pointer to store the original address of the interpretation.
    while ((ch = getc(fp)) != EOF) {
        if (isspace(ch) && !start)
            continue;
        else if (isspace(ch) && start) {
            intp->words[i] = '\0'; //add a '\0' at the end of each interpretation.
            i = 0;
            intp->next_interp = malloc(sizeof(Interp));
            intp = intp->next_interp;
            count_interp++;
            start = 0;
        }
        else if (!isspace(ch)) {
            if (!start) {
                start = 1;
                intp->words = malloc(sizeof(char));
            }
            else
                intp->words = realloc(intp->words, (i + 1) * sizeof(char));
            intp->words[i++] = ch;
        }
    }
    if (start)
        intp->words[i] = '\0';
    return intp2;
}
bool is_true(Formula f, Interpretation interp) {
    if (!f->arity)
        return logic_compare(f->word, interp); //if it's a leaf compare the word with the 'true_atoms.txt'
    else if (f->arity == 1)
        return !is_true(f->subf1, interp); //if it's a 'not' operator then return the reverse of  its result returned from its subf1.
    else if (!strcmp(f->word, "and"))
        return (is_true(f->subf1, interp) && is_true(f->subf2, interp)); //if it's an 'and' operator then return the && results of its two results returened from its subfs.
    else if (!strcmp(f->word, "or"))
        return (is_true(f->subf1, interp) || is_true(f->subf2, interp)); //if it's a 'or' operator then return the || results of its two results returened from its subfs.
    else if (!strcmp(f->word, "implies"))
        return !(is_true(f->subf1, interp) && !is_true(f->subf2, interp)); //if it's a 'implies' operator then return the results of its two result from subfs like !(subf1 && !subf2).
    else
        return (is_true(f->subf1, interp) && is_true(f->subf2, interp)) || (!is_true(f->subf1, interp) && !is_true(f->subf2, interp)); //if it's a 'iff' operator then return the results of its two results from subfs like both true or both false.
}
bool logic_compare(char atm[], Interpretation intp) {
    for (int i = 0; i < count_interp; ++i) {
        if (!strcmp(atm, intp->words))
            return true;
        intp = intp->next_interp;
    }
    return false;
}
    /*in this part, in order to look up throughout all the probabilities of combination of true atoms in the file, I use binary figures to represent this. Say if we
     * have 3 atoms then we'll have 2^3 probabilities of combinitions which are:
     *                                                                   0 0 0
     *                                                                   0 0 1
     *                                                                   0 1 0
     *                                                                   0 1 1
     *                                                                   1 0 0
     *                                                                   1 0 1
     *                                                                   1 1 0
     *                                                                   1 1 1
     * and for each 1 represents true and each 0 represents false, therefore I construct the loop like below. each time I use number of atoms corresponding to the
     * number and position of 1 in the binary figure and then check if the formula is true under that circumstance. if not move on, if it is true and it is the first
     * satisfiable combination then store them in the 'witnesses_satisfiability.txt', then move on. In the latter satisfiable combination, if the number of its atoms
     * smaller than the former one, then change it, otherwise doing nothing.*/
bool is_satisfiable(Formula f) {
    bool is_satisfy = false; //the variable which will be returned in the end of this function.
    get_unit(f); //put the atoms in the tree leaves into a pointer to pointer space.
    int count_wit = 0; //count the number of candidate atoms which are put into the 'witnesses_satisfiability.txt'.
    for (int i = 0; i < pow(2, candidates); ++i) {
        count_interp = 0;
        Interpretation intp = malloc(sizeof(Interp));
        Interpretation intp2 = intp; //use another pointer to store the original address of new interpretation which will be changed later with the programming.
        int k = i; //use another index to record the value of i, because the value i is used in the top of the loop, which is not allowed to be changed here.
        for (int j = 0; j < candidates; ++j, k /= 2) {
            if (k % 2) {
                count_interp++;
                intp->words = malloc((strlen(unit[j]) + 1) * sizeof(char));
                intp->next_interp = malloc(sizeof(Interp));
                strcpy(intp->words, unit[j]);
                intp = intp->next_interp;
            }
        }
        if (is_true(f, intp2)) {
            is_satisfy = true;
            if (!count_wit || count_interp < count_wit) {
                count_wit = count_interp;
                print_witness(intp2, count_wit);
            }
        }
    }
    return is_satisfy;
}
void get_unit(Formula f) {
    bool is_repeat = false; //used to check if there is repeats in the atoms, if so ,keep only one copy.
    if (!f->arity) {
        for (int j = 0; j < candidates; ++j) {
            if (!strcmp(unit[j], f->word))
                is_repeat = true;
        }
        if (!is_repeat) {
            if (!candidates)
                unit = malloc(sizeof(char *));
            else
                unit = realloc(unit, (candidates + 1) * sizeof(char *));
            unit[candidates] = malloc((strlen(f->word) + 1) * sizeof(char));
            strcpy(unit[candidates++], f->word);
        }
    }
    else if (f->arity == 1)
        get_unit(f->subf1);
    else {
        get_unit(f->subf1);
        get_unit(f->subf2);
    }
}
/*This part is used to print out the satisfiable combination into the file 'witnesses_satisfiability.txt'*/
void print_witness(Interpretation intp, int num_of_minimal_interp) {
    FILE *file_output = fopen("witnesses_satisfiability.txt", "w");
    for (int i = 0; i < num_of_minimal_interp; ++i) {
        fprintf(file_output, "%s\n", intp->words);
        intp = intp->next_interp;
    }
    fclose(file_output);
}
