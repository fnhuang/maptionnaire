import logging
import pandas
import math
import numpy
import operator
from scipy.stats import ttest_ind
import nltk
from nltk.tokenize import word_tokenize, sent_tokenize
from nltk.corpus import stopwords
from nltk.stem import WordNetLemmatizer
import string
import sys,os, csv

logging.basicConfig(level=logging.INFO)
ADJ = ["JJ", "JJR", "JJS"]
NOUN = ["NN", "NNS", "NNP", "NPS"]

def rank_word_in_sentences(sentences):
    word_dict = {}
    adj_dict = {}
    noun_dict = {}

    for sentence in sentences:
        sentence = sentence.lower()

        for p in nltk.pos_tag(word_tokenize(sentence)):
            if p[1] in ADJ:
                adj_dict.setdefault(p[0], 0)
                adj_dict[p[0]] += 1
            elif p[1] in NOUN:
                noun_dict.setdefault(p[0], 0)
                noun_dict[p[0]] += 1

            word_dict.setdefault(p[0], 0)
            word_dict[p[0]] += 1

    sorted_word = sorted(word_dict.items(), key=operator.itemgetter(1), reverse=True)
    sorted_adj = sorted(adj_dict.items(), key=operator.itemgetter(1), reverse=True)
    sorted_noun = sorted(noun_dict.items(), key=operator.itemgetter(1), reverse=True)

    return sorted_word, sorted_adj, sorted_noun

def basic_preprocess_text(text):
    # step 1: lower the text
    text = text.lower()

    # step 2: sentence tokenize the text for easy processing
    # this also removes extra white spaces between sentences
    sentences = sent_tokenize(text)

    concise_sentences = []

    for s in sentences:

        # step 1: remove punctuations
        for p in string.punctuation:
            s = s.replace(p,"")

        # step 2: word tokenize
        # this also remove extra white spaces in a word
        words = [w for w in word_tokenize(s)]

        # step 3: remove stopwords
        stop_removed = [w for w in words if w not in set(stopwords.words('english'))]

        # step 4: remove digits
        digit_removed = [w for w in stop_removed if not w.isdigit()]

        # step 5: lemmatize
        stemmed = [WordNetLemmatizer().lemmatize(w) for w in digit_removed]

        # dot is added at the end
        # to keep structure of sentences
        ns = " ".join(stemmed) + "."

        concise_sentences.append(ns)

    return " ".join(concise_sentences)

def calculate_boxplot(values):
    # consist of mean, std, min, max
    boxvalues = [numpy.average(values), numpy.std(values), numpy.min(values), numpy.max(values)]
    boxvalues = [round(x, 2) for x in boxvalues]

    return boxvalues

def calculate_poi_duplicates(dir):
    id2categories = {}

    for filename in os.listdir(dir):
        if filename.endswith("csv"):
            with open(f"{dir}/{filename}","r") as csvfile:
                csvreader = csv.DictReader(csvfile)
                for row in csvreader:
                    id2categories.setdefault(row["id"], []).append(filename)

    print(id2categories["410477182"])

    with open(f"{dir}/mod_tampines_poi.csv","w", newline="") as writefile:
        csvwriter = csv.writer(writefile)

        with open(f"{dir}/tampines_poi.csv","r") as csvfile:
            csvreader = csv.DictReader(csvfile)

            csvwriter.writerow(csvreader.fieldnames)

            for row in csvreader:
                id = row["id"]
                if len(id2categories[id]) == 2 and "tampines_poi.csv" in id2categories[id]:
                    id2categories.pop(id)
                else:
                    csvwriter.writerow(row.values())

    for id in id2categories:
        if len(id2categories[id]) > 1:
            logging.info(f"{id},{id2categories[id]}")


class DStat():
    def __init__(self, data_file):

        #first row of data file should be a column index
        #column index does not need to be sequential
        #column index can start from any number
        #column index has to be different between columns
        #column index has to be integer
        self.pd_data = pandas.read_csv(data_file)
        self.pd_data.columns = self.pd_data.columns.astype(int)



    def _get_var2nomvals(self, var_col_idx, data_col_idx):

        # list of nominal values for e.g. travel freq
        # (1-2 days per week, 3-4 days per week, etc)
        # keep it as a list because we want to ensure order is maintained
        nomvals= []

        # each variable has a list as its values.
        # the list contains the count of each nominal value following the order in nomvals
        var2vals = {}

        # [1:] to remove the question
        trunc_data = self.pd_data[[var_col_idx, data_col_idx]][1:]
        nomvals = [i for i in set(trunc_data[data_col_idx])]

        for row_idx, row in trunc_data.iterrows():
            # ignore header
            if row_idx > 0:
                var_group = row[var_col_idx]
                nom_val = row[data_col_idx]

                # vals will be array of values e.g. [0, 0, 0, 0, 0]
                # each value represents count of corresponding nominal value
                # arr indices of vals should correspond to array indices of nomvals
                vals = var2vals.setdefault(var_group,[0] * len(nomvals))
                vals[nomvals.index(nom_val)] += 1

        return nomvals, var2vals

    # this method get the ordinal/float values in a column and put them in a list
    def _get_scores(self, data_col_idx):
        vals = []
        trunc_data = self.pd_data[[data_col_idx]]

        for row_idx, row in trunc_data.iterrows():
            # ignore header
            if row_idx > 0:
                score = row[data_col_idx]

                # check if value is "str" -- not "NaN"
                # empty space ("") is interpreted as "NaN"
                if isinstance(row[data_col_idx], str):
                    # get the first word from answers such as "5 (most important)"
                    score = float(row[data_col_idx].split()[0])

                vals.append(score)

        return vals

    # this method group values by a variable (e.g. age group)
    def _get_var2vals(self, var_col_idx, data_col_idx):
        var2vals = {}
        trunc_data = self.pd_data[[var_col_idx, data_col_idx]]

        for row_idx, row in trunc_data.iterrows():
            # ignore header
            if row_idx > 0:
                var_group = row[var_col_idx]

                score = row[data_col_idx]

                # check if value is "str" -- not "NaN"
                # empty space ("") is interpreted as "NaN"
                if isinstance(row[data_col_idx], str):
                    # get the first word from answers such as "5 (most important)"
                    score = float(row[data_col_idx].split()[0])

                var2vals.setdefault(var_group, []).append(score)

        return var2vals

    # this method is used when data is not ordinal or continuous, but nominal
    # it returns the count of each nominal value of each variable group
    # e.g. each traveling frequency by age group
    # how many age group travels 1-2 days per week, 3-4 days per week, etc.
    def calculate_counts_of_var(self, var_col_idx, data_col_idx):
        nomvals, var2vals = self._get_var2nomvals(var_col_idx, data_col_idx)

        logging.info(f"{nomvals}")
        for var in var2vals:
            vals = var2vals[var]
            percent = [numpy.round(i*1.0/sum(vals),2) for i in vals]
            logging.info(f"{var},{list(zip(vals,percent))}")

    # param @data_col_index is the continuous or ordinal values
    # this method calculates the count/percentage of nominal values (1/2, 3, 4/5)
    def calculate_grouped_nominal_counts(self, data_col_idx):
        scores = self._get_scores(data_col_idx)
        did_not_answer = sum(math.isnan(x) for x in scores)

        low = len(list(filter(lambda x: x == 1.0 or x == 2.0, scores)))
        neu = len(list(filter(lambda x: x == 3.0, scores)))
        hig = len(list(filter(lambda x: x == 4.0 or x == 5.0, scores)))

        total = (did_not_answer + low + neu + hig) * 1.0

        logging.info("did not answer, low, neutral, high")
        logging.info(f"{did_not_answer}({round(did_not_answer/total,2)}),{low}({round(low/total,2)}),{neu}({round(neu/total,2)}), {hig}({round(hig/total,2)})")

    # param @data_col_index is the continuous or ordinal values
    # this method returns basic statistics of each variable group (e.g. age group)
    def calculate_basic_stats(self, data_col_idx):
        scores = self._get_scores(data_col_idx)
        did_not_answer = sum(math.isnan(x) for x in scores)
        answers = len(scores) - did_not_answer

        boxvalues = calculate_boxplot(list(filter(lambda x: not math.isnan(x), scores)))

        logging.info(f"{answers},{did_not_answer},{boxvalues}")

    # param @var_col_index is a variable you want to group, e.g. age
    # param @data_col_index is the continuous or ordinal values that belong to a variable group (e.g. age group)
    # this method returns basic statistics of each variable group (e.g. age group)
    def calculate_basic_stats_by_var(self, var_col_idx, data_col_idx):
        var2vals = self._get_var2vals(var_col_idx, data_col_idx)

        for var_group in var2vals:
            scores = var2vals[var_group]
            did_not_answer = sum(math.isnan(x) for x in scores)
            answers = len(scores) - did_not_answer

            boxvalues = calculate_boxplot(list(filter(lambda x: not math.isnan(x), scores)))

            logging.info(f"{var_group},{answers},{did_not_answer},{boxvalues}")

    # this method extract words from sentences
    # This method ranks these words based on frequency
    def calculate_word_counts_from_sent(self, data_col_idx):
        trunc_data = self.pd_data[[data_col_idx]]

        word_dict = {}
        adj_dict = {}
        noun_dict = {}

        sentences = []
        for row_idx, row in trunc_data.iterrows():
            # ignore header
            if row_idx > 0:
                sentence = ""
                # check if value is "str" -- not "NaN"
                # empty space ("") is interpreted as "NaN"
                if isinstance(row[data_col_idx], str):
                    sentence = row[data_col_idx]
                sentence = basic_preprocess_text(sentence)

                sentences.append(sentence)

        sorted_word, sorted_adj, sorted_noun = rank_word_in_sentences(sentences)

        logging.info(f"{sorted_word}")
        logging.info(f"{sorted_adj}")
        logging.info(f"{sorted_noun}")

    # this method treats each phrase/word/sentence in a row as a word
    # because it processes answer to the question
    # "word that means enjoyable and functional walking environment"
    # This method ranks them based on frequency
    def calculate_word_counts(self, data_col_idx):
        trunc_data = self.pd_data[[data_col_idx]]

        word_dict = {}
        adj_dict = {}
        noun_dict = {}

        for row_idx, row in trunc_data.iterrows():
            # ignore header
            if row_idx > 0:
                word = ""
                # check if value is "str" -- not "NaN"
                # empty space ("") is interpreted as "NaN"
                if isinstance(row[data_col_idx], str):
                    word = row[data_col_idx]
                word = word.lower()

                for p in nltk.pos_tag(word_tokenize(word)):
                    # if any part of the sentence is adjective
                    # take the whole word as adjective
                    if p[1] in ADJ:
                        adj_dict.setdefault(word, 0)
                        adj_dict[word] += 1
                        break

                for p in nltk.pos_tag(word_tokenize(word)):
                    # if any part of the sentence is noun
                    # take the whole word as noun
                    if p[1] in NOUN:
                        noun_dict.setdefault(word, 0)
                        noun_dict[word] += 1
                        break

                word_dict.setdefault(word, 0)
                word_dict[word] += 1

        sorted_word = sorted(word_dict.items(), key=operator.itemgetter(1), reverse=True)
        sorted_adj = sorted(adj_dict.items(), key=operator.itemgetter(1), reverse=True)
        sorted_noun = sorted(noun_dict.items(), key=operator.itemgetter(1), reverse=True)

        logging.info(f"{sorted_word}")
        logging.info(f"{sorted_adj}")
        logging.info(f"{sorted_noun}")

    # this method performs t test between values of two variable groups (e.g. two age groups)
    # It does so for all combinations of variable groups
    def get_ttest_of_var(self, var_col_idx, data_col_idx):
        var2vals = self._get_var2vals(var_col_idx, data_col_idx)

        var_group = list(var2vals.keys())

        for i in range (0, len(var_group)-1):
            i_vals = numpy.array(var2vals[var_group[i]])

            for j in range (i+1, len(var_group)):
                j_vals = numpy.array(var2vals[var_group[j]])
                ttest_ij = ttest_ind(i_vals.ravel(), j_vals.ravel())

                logging.info(f"{var_group[i]},{var_group[j]}")
                logging.info(f"{ttest_ij}")


if __name__ == "__main__" :
    calculate_poi_duplicates("C:\\Users\\fnatali\\Dropbox\\work\\lkycic\\ai_in_hc\\maptionnaire\\data\\osm")
    #dstat = DStat("data/data.csv")
    #dstat.calculate_word_counts(51)
    #dstat.calculate_word_counts_from_sent(52)
    #dstat.calculate_grouped_nominal_counts(25)
    #dstat.calculate_basic_stats(21)
    #dstat.calculate_basic_stats_by_var(2,21)
    #dstat.get_ttest_of_var(2,3)
    #dstat.calculate_counts_of_var(46,25)
    #https://geographicdata.science/book/notebooks/07_local_autocorrelation.html