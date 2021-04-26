import folium
import pandas as pd
from folium import plugins
import math
import logging, sys, csv
from collections import namedtuple
from shapely.geometry import Point, shape
from shapely.geometry.polygon import Polygon
from area import area as calc_area
import random
import descriptive_stat
import numpy
from haversine import haversine
import itertools
from collections import Counter

# LIST OF OBJECT TYPES
# happy unhappy places. HUPlace represents object HappyPlace, or UnhappyPlace
HUPlace = namedtuple("HUPlace", "respondent_id lat long coordinates happy_unhappy reason")
House = namedtuple("House", "respondent_id lat long coordinates housing_type")
NDevelop = namedtuple("NDevelop", "respondent_id improv_score thoughts suggested_changes")
ImproSuggest = namedtuple("ImproSuggest", "respondent_id coordinates type changes_proposed reason_for_change")
#pleasant and unpleasant places. PUPlace represents object PleasantPlace, or UnpleasantPlace
PUPlace = namedtuple("PUPlace", "respondent_id lat long coordinates pleasant_unpleasant reason")
Route = namedtuple("Route", "respondent_id coordinates type destination frequency route_dependency")

# participant object can be extended when you need more variables to be assessed
Participant = namedtuple("Participant", "respondent_id age_group "
                                        "data")

class Mapping():

    # all data files need to be saved in UTF-8 format: data files include
    # all files other than participant_file
    # participant file and info needs to be uploaded first
    # because data in data_files does not include only "clean" participants
    # thus it needs to be filtered by participants in participant_file
    def __init__(self, data_files, object_types, participant_file):

        self.tampines_poly = self._get_tampines_region_poly("data/tampines_region_poly.csv")

        # the index of object_arrs, data files, and object types
        # should correspond to the same objects
        # e.g. obj_arrs[0] is a list of objects
        # whose info in data_files[0]
        # belonging to type object_types[0]
        self.obj_arrs = []
        # participant profile can be reached by its ID (dictionary index)
        self.participants = {}
        self._initiateParticipant(participant_file)
        self._initiate(data_files, object_types)

    def _initiate(self, data_files, object_types):
        for i in range(0, len(data_files)):
            data = pd.read_csv(data_files[i])

            if object_types[i] == "HappyPlace":
                self._initiateHUPlace(data, "happy")
            if object_types[i] == "UnhappyPlace":
                self._initiateHUPlace(data, "unhappy")
            elif object_types[i] == "House":
                self._initiateHouse(data)
            elif object_types[i] == "NDevelop":
                self._initiateNDevelop(data)
            elif object_types[i] == "ImproSuggest":
                self._initiateImproSuggest(data)
            elif object_types[i] == "UnpleasantPlace":
                self._initiatePUPlace(data, "unpleasant")
            elif object_types[i] == "PleasantPlace":
                self._initiatePUPlace(data, "pleasant")
            elif object_types[i] == "RecreationalRoute":
                self._initiateRoute(data, "recreational")
            elif object_types[i] == "DailyRoute":
                self._initiateRoute(data, "daily")

    # data file for method below needs to be examined to ensure that
    # column corresponds to object attributes
    def _initiateParticipant(self, participant_file):
        dframe = pd.read_csv(participant_file)
        for row_idx, row in dframe.iterrows():
            # ignore header
            if row_idx > 0:
                participant_id = row["1"]

                # "2" is column index given in the header for age
                age_group = row["2"]

                # data index should refer to index given in the first row of data.csv
                # the length of the data index depends on the largest index
                # num of columns + 1 since indexing in data.csv starts from 1
                data = [0] * (len(dframe.columns) + 1)
                data[2] = row["2"] #similar to age_group

                data[25] = row["25"]; data[24] = row["24"]
                data[23] = row["23"]; data[22] = row["22"]; data[21] = row["21"]

                data[19] = row["19"]
                data[27] = row["27"]
                data[30] = row["30"]
                data[39] = row["39"]; data[40] = row["40"]; data[41] = row["41"]; data[42] = row["42"]; data[43] = row["43"]

                #gender
                data[46] = row["46"]

                data[52] = row["52"]

                self.participants[participant_id] = Participant(participant_id, age_group, data)

    # data file for method below needs to be examined to ensure that
    # column corresponds to object attributes
    def _initiateHouse(self, data):
        objs = []
        for row_idx, row in data.iterrows():
            respondent_id = row[0]

            if respondent_id in self.participants.keys():
                lat, long = [float(x) for x in row[4].split(",")]
                housing_type = row[7]
                # coordinate is structured in the form [[long,lat]]
                coordinates = [[long, lat]]
                objs.append(House(respondent_id, lat, long, coordinates, housing_type))
        self.obj_arrs.append(objs)

    # data file for method below needs to be examined to ensure that
    # column corresponds to object attributes
    def _initiateImproSuggest(self, data):
        objs = []
        for row_idx, row in data.iterrows():
            respondent_id = row[0]
            coor = row[4]

            if "[[" in coor:
                coor = coor.replace("[[\"","")
                coor = coor.replace("\"]]","")
                type = "area"
            else:
                coor = coor.replace("[\"", "")
                coor = coor.replace("\"]", "")
                type = "route"

            coors = [x for x in coor.split("\",\"")]
            # coordinates is structured in the form [[long,lat],[long,lat]]
            coordinates = [[float(c.split(",")[1]), float(c.split(",")[0])] for c in coors]

            changes_proposed = ""
            # if not str, it's "nan"
            if isinstance(row[5],str):
                changes_proposed = row[5]

            reason_for_change = ""
            # if not str, it's "nan"
            if isinstance(row[6], str):
                reason_for_change = row[6]

            objs.append(ImproSuggest(respondent_id, coordinates, type,
                                     changes_proposed, reason_for_change))
        self.obj_arrs.append(objs)

    # data file for method below needs to be examined to ensure that
    # column corresponds to object attributes
    def _initiateNDevelop(self, data):
        objs = []
        for row_idx, row in data.iterrows():
            respondent_id = row[0]

            if respondent_id in self.participants.keys():
                improv_score = float(row[7])
                thoughts = ""

                # check if value is "str" -- not "NaN"
                # empty space ("") is interpreted as "NaN"
                if isinstance(row[5], str):
                    thoughts = row[5].lower()

                suggested_changes = ""

                if isinstance(row[8], str):
                    suggested_changes = row[8].lower()

                objs.append(NDevelop(respondent_id, improv_score, thoughts, suggested_changes))

        self.obj_arrs.append(objs)

    # data file for method below needs to be examined to ensure that
    # column corresponds to object attributes
    def _initiatePUPlace(self, data, pleasant_unpleasant):
        objs = []
        for row_idx, row in data.iterrows():
            respondent_id = row[0]

            if respondent_id in self.participants.keys():
                wanted_idx = 0
                if pleasant_unpleasant == "unpleasant":
                    wanted_idx = 1

                pu_idx = float(row[5])

                # just choose the object (pleasant/unpleasant) that you need
                if pu_idx == wanted_idx:
                    lat, long = [float(x) for x in row[4].split(",")]
                    reason = row[7]
                    # coordinate is structured in the form [[long,lat]]
                    coordinates = [[long, lat]]
                    objs.append(PUPlace(respondent_id, lat, long, coordinates, pleasant_unpleasant, reason))
        self.obj_arrs.append(objs)


    def _initiateRoute(self, data, type):
        objs = []
        for row_idx, row in data.iterrows():
            respondent_id = row[0]
            coor = row[4]

            coor = coor.replace("[\"", "")
            coor = coor.replace("\"]", "")

            coors = [x for x in coor.split("\",\"")]
            # coordinates is structured in the form [[long,lat],[long,lat]]
            coordinates = [[float(c.split(",")[1]), float(c.split(",")[0])] for c in coors]

            destination = ""


            frequency = ""
            # if not str, it's "nan"
            if isinstance(row[6], str):
                frequency = row[6]

            route_dependency = ""
            # if not str, it's "nan"
            if isinstance(row[8], str):
                route_dependency = row[8]

            objs.append(Route(respondent_id, coordinates, type, destination, frequency, route_dependency))
        self.obj_arrs.append(objs)

    # data file for method below needs to be examined to ensure that
    # column corresponds to object attributes
    def _initiateHUPlace(self, data, happy_unhappy):
        objs = []
        for row_idx, row in data.iterrows():
            respondent_id = row[0]

            if respondent_id in self.participants.keys():
                lat, long = [float(x) for x in row[4].split(",")]
                reason = row[5]
                # coordinate is structured in the form [[long,lat]]
                coordinates = [[long, lat]]
                objs.append(HUPlace(respondent_id, lat, long, coordinates, happy_unhappy, reason))
        self.obj_arrs.append(objs)

    def _get_tampines_region_poly(self, poly_file):
        tampines_poly = {}
        with open(poly_file,"r") as reader:
            lines = reader.readlines()

            for line in lines[1:]:
                data = line.split(",")
                region = data[0]
                polygon = data[2].split(";")

                # coordinates are stored in the form of [[[long,lat],[long,lat],...]]]
                # there are double brackets, because sometimes certain region can include different encolsed areas
                # for example, north east region in singapore can include an enclosed area in the mainland
                # It can also includes several islands outside the mainland
                coords = []
                geocs =[[float(geoc.split("-")[0]),float(geoc.split("-")[1])] for poly in polygon for geoc in poly.split(",")]
                coords.extend(geocs)

                tampines_poly.setdefault(region,[]).append(coords)

        return tampines_poly

    # obj_arr_indices specify which list of objects you want to perform
    # this method on.
    # obj_arr_names specify what name to save the result of the method
    # performed on the list of obj specified by the idx.
    # filename will carry .html automatically.
    def create_heat_map(self, obj_arr_indices, obj_arr_names):
        m1 = folium.Map(location=[1.348919, 103.948600], zoom_start=14)

        for idx in obj_arr_indices:
            objs = self.obj_arrs[idx]
            heatmap_distribution = []

            for obj in objs:
                heatmap_distribution.append([obj.lat, obj.long])

            plugins.HeatMap(heatmap_distribution).add_to(m1)
            m1.save(f"{obj_arr_names[idx]}.html")

    def _get_participant2objects_dict(self, obj_idx):

        obj_arr = self.obj_arrs[obj_idx]
        participant2objects = {}

        for obj in obj_arr:
            # self.participants is a dictionary
            if obj.respondent_id in self.participants:
                participant2objects.setdefault(obj.respondent_id, []).append(obj)

        return participant2objects

    def _get_region_from_coord(self, lat, long):
        p = Point(long, lat)

        region = "Other"

        for poly in self.tampines_poly["North"]:
            if Polygon(poly).contains(p):
                region = "North"

        for poly in self.tampines_poly["Changkat"]:
            if Polygon(poly).contains(p):
                region = "Changkat"

        for poly in self.tampines_poly["East"]:
            if Polygon(poly).contains(p):
                region = "East"

        for poly in self.tampines_poly["West"]:
            if Polygon(poly).contains(p):
                region = "West"

        for poly in self.tampines_poly["Central"]:
            if Polygon(poly).contains(p):
                region = "Central"

        return region

    def _get_region2nomvals(self, obj_idx, data_col_idx):
        # list of nominal values for e.g. travel freq
        # (1-2 days per week, 3-4 days per week, etc)
        # keep it as a list because we want to ensure order is maintained
        nomvals = []

        # each variable has a list as its values.
        # the list contains the count of each nominal value following the order in nomvals
        var2nomvals = {}

        participant2objects = self._get_participant2objects_dict(obj_idx)

        # set nomvals
        for participant_id in participant2objects:
            # get the nominal answer of the participant
            nomval = self.participants[participant_id].data[data_col_idx]

            if nomval not in nomvals:
                nomvals.append(nomval)

        # set region2nomvals
        for participant_id in participant2objects:
            objects = participant2objects[participant_id]
            region = self._get_region_given_regobjects(objects)

            nom_val = self.participants[participant_id].data[data_col_idx]

            # vals will be array of values e.g. [0, 0, 0, 0, 0]
            # each value represents count of corresponding nominal value
            # arr indices of vals should correspond to array indices of nomvals
            vals = var2nomvals.setdefault(region, [0] * len(nomvals))
            vals[nomvals.index(nom_val)] += 1

        return nomvals, var2nomvals

    def _get_mapobj_attr_value(self, objects, attribute):
        object = objects[0]
        val = getattr(object, attribute)
        if not isinstance(val, str):
            val = "Not available"

        # if there are more than 1 houses
        if len(objects) > 1:
            values = set([val])

            # loop through objects skipping the first one, as
            # the housing type of the first object has been assessed
            for i in range(1, len(objects)):
                values.add(getattr(objects[i], attribute))

            # if there are more than 1 houses, and they are of the same housing type
            # we use the housing type, as there is no contradiction
            if len(values) == 1:
                val = list(values)[0]

                #if value not available, it was extracted as nan (float) by panda
                if not isinstance(val, str):
                    val = "Not available"
            # housing type more than 1
            else:
                val = "More than 1"

        return val

    def _get_hsetype2nomvals(self, hse_idx, data_col_idx):
        # list of nominal values for e.g. travel freq
        # (1-2 days per week, 3-4 days per week, etc)
        # keep it as a list because we want to ensure order is maintained
        nomvals = []

        # each variable has a list as its values.
        # the list contains the count of each nominal value following the order in nomvals
        var2nomvals = {}

        participant2objects = self._get_participant2objects_dict(hse_idx)

        # set nomvals
        for participant_id in participant2objects:
            # get the nominal answer of the participant
            nomval = self.participants[participant_id].data[data_col_idx]

            if nomval not in nomvals:
                nomvals.append(nomval)

        # set var2nomvals
        for participant_id in participant2objects:
            objects = participant2objects[participant_id]

            housing_type = self._get_mapobj_attr_value(objects,"housing_type")

            nom_val = self.participants[participant_id].data[data_col_idx]

            # vals will be array of values e.g. [0, 0, 0, 0, 0]
            # each value represents count of corresponding nominal value
            # arr indices of vals should correspond to array indices of nomvals
            vals = var2nomvals.setdefault(housing_type, [0] * len(nomvals))
            vals[nomvals.index(nom_val)] += 1

        return nomvals, var2nomvals

    # this method categorize values by housing type
    # data_col_idx is the data you want to calculate basic statistics on
    # hse_idx refers to the index of the obj_arr in which the house objects reside
    def _get_hsetype2vals(self, hse_idx, data_col_idx):
        hsetype2vals = {}

        participant2objects = self._get_participant2objects_dict(hse_idx)

        # looping through all participants
        for participant_id in participant2objects:
            objects = participant2objects[participant_id]

            housing_type = self._get_mapobj_attr_value(objects, "housing_type")

            score = self.participants[participant_id].data[data_col_idx]

            # check if value is "str" -- not "NaN"
            # empty space ("") is interpreted as "NaN"
            if isinstance(score, str):
                # get the first word from answers such as "5 (most important)"
                score = float(score.split()[0])

            hsetype2vals.setdefault(housing_type, []).append(score)

        return hsetype2vals

    # this method categorize mapobj nominal values by region of regobj_idx
    # for e.g. what are the values of "reason_for_changes" of object 'Improvement Suggestion"
    # for people living in Tampines North
    def _get_region2mapobjnomvals(self, regobj_idx, mapobj_idx, mapobj_attr):
        # list of nominal values for e.g. travel freq
        # (1-2 days per week, 3-4 days per week, etc)
        # keep it as a list because we want to ensure order is maintained
        nomvals = []

        # each variable has a list as its values.
        # the list contains the count of each nominal value following the order in nomvals
        reg2nomvals = {}

        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # set nomvals
        for participant_id in participant2mapobjects:
            # get the nominal answer of the participant
            objects = participant2mapobjects[participant_id]
            nomval = ""
            for obj in objects:
                nomval += getattr(obj, mapobj_attr)

            # 1 participant can be mapped to 2 objects, thus
            # combine the nomval
            if nomval not in nomvals:
                nomvals.append(nomval)

        # set reg2nomvals
        for participant_id in participant2regobjects:
            objects = participant2regobjects[participant_id]

            region = self._get_region_given_regobjects(objects)

            # 1 participant can be mapped to 2 objects, thus
            # combine the nomval
            objects = participant2mapobjects[participant_id]
            nomval = ""
            for obj in objects:
                nomval += getattr(obj, mapobj_attr)


            # vals will be array of values e.g. [0, 0, 0, 0, 0]
            # each value represents count of corresponding nominal value
            # arr indices of vals should correspond to array indices of nomvals
            vals = reg2nomvals.setdefault(region, [0] * len(nomvals))
            vals[nomvals.index(nomval)] += 1

        return nomvals, reg2nomvals

    # this method categorize values by region
    # for e.g. what are the values of "walking experience" for people living in Tampines North
    # data_col_idx is the data you want to calculate basic statistics on
    # obj_idx refers to the index of the obj_arr you initate in obj_arrs
    # the obj_arr refers to the objects whose region you need, for e.g. house
    def _get_region2vals(self, obj_idx, data_col_idx):
        region2vals = {}

        participant2objects = self._get_participant2objects_dict(obj_idx)

        #looping through all participants
        for participant_id in participant2objects:
            objects = participant2objects[participant_id]

            region = self._get_region_given_regobjects(objects)

            score = self.participants[participant_id].data[data_col_idx]

            # check if value is "str" -- not "NaN"
            # empty space ("") is interpreted as "NaN"
            if isinstance(score, str):
                # get the first word from answers such as "5 (most important)"
                score = float(score.split()[0])

            region2vals.setdefault(region, []).append(score)


        return region2vals

    # data_col_idx is the participant data you want to calculate basic statistics on
    # hse_idx refers to the index of the obj_arr in which the house objects reside
    def calculate_participant_stats_by_housing_type(self, hse_idx, data_col_idx):
        hsetype2vals = self._get_hsetype2vals(hse_idx, data_col_idx)

        for hsetype in hsetype2vals:
            scores = hsetype2vals[hsetype]
            did_not_answer = sum(math.isnan(x) for x in scores)
            answers = len(scores) - did_not_answer

            boxvalues = descriptive_stat.calculate_boxplot(list(filter(lambda x: not math.isnan(x), scores)))

            logging.info(f"{hsetype},{answers},{did_not_answer},{boxvalues}")

    # this method is used when participant data is not ordinal or continuous, but nominal
    # it returns the count of each nominal value of each variable group
    # e.g. each traveling frequency by age group
    # how many age group travels 1-2 days per week, 3-4 days per week, etc.
    def calculate_counts_of_parvar_by_region(self, obj_idx, data_col_idx):
        nomvals, var2vals = self._get_region2nomvals(obj_idx, data_col_idx)

        logging.info(f"{nomvals}")
        for var in var2vals:
            vals = var2vals[var]
            percent = [numpy.round(i * 1.0 / sum(vals), 2) for i in vals]
            logging.info(f"{var},{list(zip(vals,percent))}")

    # this method is used when participant data is not ordinal or continuous, but nominal
    # it returns the count of each nominal value of each variable group
    # e.g. each traveling frequency by age group
    # how many age group travels 1-2 days per week, 3-4 days per week, etc.
    def calculate_counts_of_parvar_by_housing_type(self, obj_idx, data_col_idx):
        nomvals, var2vals = self._get_hsetype2nomvals(obj_idx, data_col_idx)

        logging.info(f"{nomvals}")
        for var in var2vals:
            vals = var2vals[var]
            percent = [numpy.round(i * 1.0 / sum(vals), 2) for i in vals]
            logging.info(f"{var},{list(zip(vals,percent))}")

    def _get_nominal_values(self, obj_idx, attribute):
        participant2objects = self._get_participant2objects_dict(obj_idx)

        nom_vals = []
        for participant_id in participant2objects:
            objs = participant2objects[participant_id]
            for obj in objs:
                nom_val = getattr(obj, attribute)
                nom_vals.append(nom_val)

        nomstats = dict(Counter(nom_vals))

        return nomstats

    def _get_scores(self, obj_idx, attribute):
        participant2objects = self._get_participant2objects_dict(obj_idx)

        scores = []
        for participant_id in participant2objects:
            obj = participant2objects[participant_id][0]
            score = getattr(obj, attribute)

            # check if value is "str" -- not "NaN"
            # empty space ("") is interpreted as "NaN"
            if isinstance(score, str):
                # get the first word from answers such as "5 (most important)"
                score = float(score.split()[0])

            scores.append(score)

        return scores

    # this method creates a geojson object from the list of coordinates.
    # coordinates should be in this format [[long,lat],[long,lat]]
    def _create_area_geom(self, coordinates):
        geom = {}
        geom["type"] = 'Polygon'
        geom["coordinates"] = [coordinates]

        return geom

    def calculate_area(self, obj_idx):
        participant2objects = self._get_participant2objects_dict(obj_idx)

        areas = []

        for participant_id in participant2objects:
            objs = participant2objects[participant_id]
            for obj in objs:
                geom = self._create_area_geom(obj.coordinates)
                area = calc_area(geom)

                areas.append(area)

        wrong_mapping = len([a for a in areas if a == 0])

        logging.info("correct mapping", "wrong mapping", "aavg", "std", "min", "max")
        logging.info(f"{len(areas)-wrong_mapping},{wrong_mapping},"
                     f"{round(numpy.average(areas),2)},{round(numpy.std(areas),2)},"
                     f"{round(numpy.min(areas),2)},{round(numpy.max(areas),2)}")

    # point should be in this format [long,lat]
    # lines should be in this format [[long,lat],[long,lat]]
    def _calculate_shortest_distance_of_point_to_line(self, point, lines):
        # assuming flat surface
        # code has been tested and relatively accurate (minor differences) up to 90 km distance
        # assumption works better even for shorter distances
        y1,x1 = lines[0][0], lines[0][1]
        y2,x2 = lines[1][0], lines[1][1]
        y0,x0 = point[0], point[1]

        # get a perpendicular projection of point on the line
        if x2 == x1:
            x = x1
            y = y0
        elif y2 == y1:
            y = y1
            x = x0
        else:
            m = (y2 - y1) / (x2 - x1)
            mp = -1.0 / m

            # projected coordinates
            x = (y1 - m * x1 - y0 + mp * x0) / (mp - m)
            y = mp * x + (y0 - mp * x0)


        # projected coordinate needs to be within the line
        if not (x >= min(x1,x2) and x <= max(x1,x2) and y >= min(y1,y2) and y <= max(y1,y2)):
            # if projection is not on the line
            # (line is too short to cover the perpendicular projection of the point)
            distance = -1
        else:
            distance = self._calculate_haversine([[y,x],[y0,x0]])

        #print(distance)
        return [y,x],distance


    # this method calculate the distance between a list of coordinates.
    # coordinates should be in this format [[long,lat],[long,lat]]
    def _calculate_haversine(self, coordinates):
        distance = 0
        for i in range(0, len(coordinates)-1):
            point_a = (coordinates[i][1], coordinates[i][0]) # (lat, lon)
            point_b = (coordinates[i+1][1], coordinates[i+1][0])

            distance += haversine(point_a, point_b) * 1000 # in m

        return distance

    def calculate_distance(self, obj_idx):
        participant2objects = self._get_participant2objects_dict(obj_idx)

        distances = []

        for participant_id in participant2objects:
            objs = participant2objects[participant_id]
            for obj in objs:
                distance = self._calculate_haversine(obj.coordinates)
                distances.append(distance)

        wrong_mapping = len([d for d in distances if d == 0])

        logging.info("correct mapping, wrong mapping, average, std, min, max")
        logging.info(f"{len(distances)-wrong_mapping},{wrong_mapping},"
                     f"{round(numpy.average(distances),2)},{round(numpy.std(distances),2)},"
                     f"{round(numpy.min(distances),2)},{round(numpy.max(distances),2)}")

    def _get_region_given_regobjects(self, regobjects):
        object = regobjects[0]
        region = self._get_region_from_coord(object.lat, object.long)

        # if there are more than 1 houses
        if len(regobjects) > 1:
            regions = set([region])

            # loop through objects skipping the first one, as
            # the region of the first object has been assessed
            for i in range(1, len(regobjects)):
                r = self._get_region_from_coord(regobjects[i].lat, regobjects[i].long)
                regions.add(r)

            # if there are more than 1 houses, and they are from the same region
            # we use the region, as there is no contradiction
            if len(regions) == 1:
                region = list(regions)[0]
            else:
                region = "More than 1 Houses"

        return region


    #nominal counts refer to the counts of a nominal values of mapobj_attr of mapobj "mapobj_idx"
    #groupattr and groupobj_idx specify the attr of mapobj "groupobj_idx" by which you want to group your results
    def calculate_nominal_counts_by_mapobjattr(self, groupobj_idx, group_attr, mapobj_idx, mapobj_attr):
        # participant-house_objects
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        group2nomvals = {}

        for participant_id in participant2groupobjects:
            group_objs = participant2groupobjects[participant_id]

            # get the group of participant "participant_id"
            group = self._get_mapobj_attr_value(group_objs, group_attr)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                nom_val = ""
                for obj in objs:
                    raw = getattr(obj, mapobj_attr)
                    if isinstance(raw, str):
                        nom_val = raw

                    nomvals = group2nomvals.setdefault(group, {})
                    nomvals[nom_val] = nomvals.setdefault(nom_val, 0) + 1

        for group in group2nomvals:
            nomstats = group2nomvals[group]
            summary_stat = [(x, nomstats[x], round(nomstats[x] / sum(nomstats.values()), 2)) for x in nomstats.keys()]
            logging.info(f"{group},{summary_stat}")





    def calculate_distance_by_mapobjattr(self, groupobj_idx, group_attr, mapobj_idx):
        # participant-house_objects
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # num of mapobjects of each participant
        group2distances = {}

        for participant_id in participant2groupobjects:
            group_objs = participant2groupobjects[participant_id]

            # get the group of participant "participant_id"
            group = self._get_mapobj_attr_value(group_objs, group_attr)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                for obj in objs:
                    distance = self._calculate_haversine(obj.coordinates)

                    distances = group2distances.setdefault(group, [])
                    distances.append(distance)

        for group in group2distances:
            logging.info(
                f"{group},{round(numpy.average(group2distances[group]),2)},{round(numpy.std(group2distances[group]),2)},"
                f"{round(numpy.min(group2distances[group]),2)},{round(numpy.max(group2distances[group]),2)}")

    def calculate_distance_by_pardata(self, pardata_idx, mapobj_idx):
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # num of mapobjects of each participant
        group2distances = {}

        for participant_id in self.participants:
            group = self.participants[participant_id].data[pardata_idx]

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                for obj in objs:
                    distance = self._calculate_haversine(obj.coordinates)

                    distances = group2distances.setdefault(group, [])
                    distances.append(distance)

        for group in group2distances:
            logging.info(f"{group},{round(numpy.average(group2distances[group]),2)},{round(numpy.std(group2distances[group]),2)},"
                         f"{round(numpy.min(group2distances[group]),2)},{round(numpy.max(group2distances[group]),2)}")

    def calculate_distance_by_region(self, regobj_idx, mapobj_idx):
        # participant-house_objects
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # num of mapobjects of each participant
        reg2distances = {}

        for participant_id in participant2regobjects:
            regobjects = participant2regobjects[participant_id]
            #get the region of participant "participant_id"
            region = self._get_region_given_regobjects(regobjects)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                for obj in objs:
                    distance = self._calculate_haversine(obj.coordinates)

                    distances = reg2distances.setdefault(region, [])
                    distances.append(distance)

        for reg in reg2distances:
            logging.info(f"{reg},{round(numpy.average(reg2distances[reg]),2)},{round(numpy.std(reg2distances[reg]),2)},"
                         f"{round(numpy.min(reg2distances[reg]),2)},{round(numpy.max(reg2distances[reg]),2)}")

    def calculate_area_by_mapobjattr(self, groupobj_idx, group_attr, mapobj_idx):
        # participant-house_objects
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # num of mapobjects of each participant
        group2areas = {}

        for participant_id in participant2groupobjects:
            group_objs = participant2groupobjects[participant_id]

            # get the group of participant "participant_id"
            group = self._get_mapobj_attr_value(group_objs, group_attr)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                for obj in objs:
                    geom = self._create_area_geom(obj.coordinates)
                    area = calc_area(geom)

                    areas = group2areas.setdefault(group, [])
                    areas.append(area)

        for group in group2areas:
            logging.info(
                f"{group},{round(numpy.average(group2areas[group]),2)},{round(numpy.std(group2areas[group]),2)},"
                f"{round(numpy.min(group2areas[group]),2)},{round(numpy.max(group2areas[group]),2)}")

    def calculate_area_by_pardata(self, pardata_idx, mapobj_idx):
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # num of mapobjects of each participant
        group2areas = {}

        for participant_id in self.participants:
            group = self.participants[participant_id].data[pardata_idx]

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                for obj in objs:
                    geom = self._create_area_geom(obj.coordinates)
                    area = calc_area(geom)

                    areas = group2areas.setdefault(group, [])
                    areas.append(area)

        for group in group2areas:
            logging.info(f"{group},{round(numpy.average(group2areas[group]),2)},{round(numpy.std(group2areas[group]),2)},"
                         f"{round(numpy.min(group2areas[group]),2)},{round(numpy.max(group2areas[group]),2)}")

    def calculate_area_by_region(self, regobj_idx, mapobj_idx):
        # participant-house_objects
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # num of mapobjects of each participant
        reg2areas = {}

        for participant_id in participant2regobjects:
            regobjects = participant2regobjects[participant_id]
            #get the region of participant "participant_id"
            region = self._get_region_given_regobjects(regobjects)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                for obj in objs:
                    geom = self._create_area_geom(obj.coordinates)
                    area = calc_area(geom)

                    areas = reg2areas.setdefault(region, [])
                    areas.append(area)

        for reg in reg2areas:
            logging.info(f"{reg},{round(numpy.average(reg2areas[reg]),2)},{round(numpy.std(reg2areas[reg]),2)},"
                         f"{round(numpy.min(reg2areas[reg]),2)},{round(numpy.max(reg2areas[reg]),2)}")

    # groupobj and group_attr refers to the attribute "group_attr"
    # of object "groupobj_idx" by which you want to group the statistics/answers
    def count_mapobj_by_mapobjattr(self, groupobj_idx, group_attr, mapobj_idx):
        # participant-house_objects
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # all the stats you want to display
        group2count = {}
        # num of mapobjects of each participant
        group2answers = {}
        for participant_id in participant2groupobjects:
            group_objs = participant2groupobjects[participant_id]
            # get the region of participant "participant_id"
            group = self._get_mapobj_attr_value(group_objs, group_attr)

            # get stats you want to display for region "region". set it to 0 by default
            values = group2count.setdefault(group, [0] * 9)

            # get num of objects of participants staying in region "region"
            answers = group2answers.setdefault(group, [])

            # participant answers the question and has the map objects
            if participant_id in participant2mapobjects:
                # answering
                values[2] += 1
                # total
                values[4] += len(participant2mapobjects[participant_id])
                answers.append(len(participant2mapobjects[participant_id]))
            else:
                # not answering
                values[0] += 1

        logging.info("not answering,%,answering,%,total answers,mean,std,min,max")
        for group in group2count:
            # % not answering & answering
            group2count[group][1] = group2count[group][0] * 1.0 / (group2count[group][0] + group2count[group][2])
            group2count[group][1] = round(group2count[group][1], 2)

            group2count[group][3] = group2count[group][2] * 1.0 / (group2count[group][0] + group2count[group][2])
            group2count[group][3] = round(group2count[group][3], 2)

            # mean
            group2count[group][5] = round(numpy.average(group2answers[group]), 2)

            # std
            group2count[group][6] = round(numpy.std(group2answers[group]), 2)

            # if total answers > 0
            if group2count[group][4] > 0:
                group2count[group][7] = round(numpy.min(group2answers[group]), 2)
                group2count[group][8] = round(numpy.max(group2answers[group]), 2)

            logging.info(f"{group},{group2count[group]}")

    # how many participants answer to the question
    # that requires them to create mapobj "mapobj_idx"
    # result is grouped by participant's attributes pardata_idx, e.g. age
    def count_mapobj_by_pardata(self, pardata_idx, mapobj_idx):
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        # all the stats you want to display
        group2count = {}
        # num of mapobjects of each participant
        group2answers = {}


        for participant_id in self.participants:
            group = self.participants[participant_id].data[pardata_idx]

            # get stats you want to display for group "group". set it to 0 by default
            values = group2count.setdefault(group, [0] * 9)

            # get num of objects of participants staying in region "region"
            answers = group2answers.setdefault(group, [])

            # participant answers the question and has the map objects
            if participant_id in participant2mapobjects:
                # answering
                values[2] += 1
                # total
                values[4] += len(participant2mapobjects[participant_id])
                answers.append(len(participant2mapobjects[participant_id]))
            else:
                # not answering
                values[0] += 1

        logging.info("not answering,%,answering,%,total answers,mean,std,min,max")
        for group in group2count:
            # % not answering & answering
            group2count[group][1] = group2count[group][0] * 1.0 / (group2count[group][0] + group2count[group][2])
            group2count[group][1] = round(group2count[group][1], 2)

            group2count[group][3] = group2count[group][2] * 1.0 / (group2count[group][0] + group2count[group][2])
            group2count[group][3] = round(group2count[group][3], 2)

            # mean
            group2count[group][5] = round(numpy.average(group2answers[group]), 2)

            # std
            group2count[group][6] = round(numpy.std(group2answers[group]), 2)

            #if answers are not empty
            if group2count[group][4] > 0:
                group2count[group][7] = round(numpy.min(group2answers[group]), 2)
                group2count[group][8] = round(numpy.max(group2answers[group]), 2)

            logging.info(f"{group},{group2count[group]}")

    # how many participants answer to the question
    # that requires them to create mapobj "mapobj_idx"
    def count_mapobj_by_region(self, regobj_idx, mapobj_idx):
        #participant-house_objects
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        #participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        #all the stats you want to display
        reg2count = {}
        #num of mapobjects of each participant
        reg2answers = {}
        for participant_id in participant2regobjects:
            regobjects = participant2regobjects[participant_id]
            #get the region of participant "participant_id"
            region = self._get_region_given_regobjects(regobjects)

            #get stats you want to display for region "region". set it to 0 by default
            values = reg2count.setdefault(region, [0]*9)

            #get num of objects of participants staying in region "region"
            answers = reg2answers.setdefault(region, [])

            #participant answers the question and has the map objects
            if participant_id in participant2mapobjects:
                #answering
                values[2] += 1
                #total
                values[4] += len(participant2mapobjects[participant_id])
                answers.append(len(participant2mapobjects[participant_id]))
            else:
                #not answering
                values[0] += 1

        logging.info("not answering,%,answering,%,total answers,mean,std,min,max")
        for reg in reg2count:
            #% not answering & answering
            reg2count[reg][1] = reg2count[reg][0] * 1.0 / (reg2count[reg][0] + reg2count[reg][2])
            reg2count[reg][1] = round(reg2count[reg][1], 2)

            reg2count[reg][3] = reg2count[reg][2] * 1.0 / (reg2count[reg][0] + reg2count[reg][2])
            reg2count[reg][3] = round(reg2count[reg][3], 2)

            #mean
            reg2count[reg][5] = round(numpy.average(reg2answers[reg]),2)

            #std
            reg2count[reg][6] = round(numpy.std(reg2answers[reg]),2)

            if reg2count[reg][4] > 0:
                reg2count[reg][7] = round(numpy.min(reg2answers[reg]), 2)
                reg2count[reg][8] = round(numpy.max(reg2answers[reg]), 2)


            logging.info(f"{reg},{reg2count[reg]}")

    def _get_facilities(self, poi_file):
        facility_dict = {}
        facilities = set([])

        with open(poi_file, "r") as csvfile:
            csvreader = csv.DictReader(csvfile)

            for row in csvreader:
                id = row["id"]
                type = row["type"]
                coordinate = [float(row["long"]), float(row["lat"])]

                values = facility_dict.setdefault(id, [])
                values.append(type)
                values.append(coordinate)

                facilities.add(type)

        return facilities, facility_dict

    def calculate_facilities_around_map_obj_by_mapobjattr(self, poi_file, groupobj_idx, group_attr, mapobj_idx):
        facilities, facility_dict = self._get_facilities(poi_file)
        participant2objects = self._get_participant2objects_dict(mapobj_idx)
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)

        total_facility_count_by_group = {}

        participant_count = 0

        for participant_id in participant2groupobjects:
            group_objs = participant2groupobjects[participant_id]
            group = self._get_mapobj_attr_value(group_objs, group_attr)

            total_facility_count = total_facility_count_by_group.setdefault(group, {})

            participant_count += 1

            if participant_id in participant2objects:

                # logging.info(f"Processing participant {participant_count} out of {len(participant2objects)}")
                # for each marked place, e.g. happy place
                for obj in participant2objects[participant_id]:
                    # need to be set in the beginning because we want to have 0 values
                    # if facility counts (e.g. food place counts)
                    # #=surrounding that map object (e.g. a happy place) is 0
                    facility_count = {f: 0 for f in facilities}

                    coord1 = obj.coordinates[0]

                    for facility_id in facility_dict:
                        type = facility_dict[facility_id][0]
                        coord2 = facility_dict[facility_id][1]

                        distance = self._calculate_haversine([coord1, coord2])
                        if distance <= 500:
                            facility_count[type] = facility_count[type] + 1

                    # we need to know facility counts for each marked place, e.g. happy place
                    for type in facility_count:
                        vals = total_facility_count.setdefault(type, [])
                        vals.append(facility_count[type])

        for group in total_facility_count_by_group:
            logging.info(f"{group}")
            total_facility_count = total_facility_count_by_group[group]

            for type in total_facility_count:
                vals = total_facility_count[type]

                logging.info(f"{type},{round(numpy.average(vals),2)},{round(numpy.std(vals),2)},"
                             f"{round(numpy.min(vals),2)},{round(numpy.max(vals),2)}")


    def calculate_facilities_around_map_obj_by_pardata(self,poi_file,pardata_idx,obj_idx):
        facilities, facility_dict = self._get_facilities(poi_file)
        participant2objects = self._get_participant2objects_dict(obj_idx)

        total_facility_count_by_group = {}

        participant_count = 0


        for participant_id in self.participants:
            group = self.participants[participant_id].data[pardata_idx]

            total_facility_count = total_facility_count_by_group.setdefault(group,{})

            participant_count += 1

            if participant_id in participant2objects:

                # logging.info(f"Processing participant {participant_count} out of {len(participant2objects)}")
                # for each marked place, e.g. happy place
                for obj in participant2objects[participant_id]:
                    # need to be set in the beginning because we want to have 0 values
                    # if facility counts (e.g. food place counts)
                    # #=surrounding that map object (e.g. a happy place) is 0
                    facility_count = {f: 0 for f in facilities}

                    coord1 = obj.coordinates[0]

                    for facility_id in facility_dict:
                        type = facility_dict[facility_id][0]
                        coord2 = facility_dict[facility_id][1]

                        distance = self._calculate_haversine([coord1, coord2])
                        if distance <= 500:
                            facility_count[type] = facility_count[type] + 1

                    # we need to know facility counts for each marked place, e.g. happy place
                    for type in facility_count:
                        vals = total_facility_count.setdefault(type, [])
                        vals.append(facility_count[type])

        for group in total_facility_count_by_group:
            logging.info(f"{group}")
            total_facility_count = total_facility_count_by_group[group]

            for type in total_facility_count:
                vals = total_facility_count[type]

                logging.info(f"{type},{round(numpy.average(vals),2)},{round(numpy.std(vals),2)},"
                             f"{round(numpy.min(vals),2)},{round(numpy.max(vals),2)}")

    def calculate_facilities_around_map_obj_by_region(self,poi_file,regobj_idx,obj_idx):
        facilities, facility_dict = self._get_facilities(poi_file)
        participant2objects = self._get_participant2objects_dict(obj_idx)
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)

        total_facility_count_by_group = {}

        participant_count = 0


        for participant_id in participant2regobjects:
            regobjects = participant2regobjects[participant_id]
            # get the region of participant "participant_id"
            region = self._get_region_given_regobjects(regobjects)

            total_facility_count = total_facility_count_by_group.setdefault(region,{})

            participant_count += 1

            if participant_id in participant2objects:

                # logging.info(f"Processing participant {participant_count} out of {len(participant2objects)}")
                # for each marked place, e.g. happy place
                for obj in participant2objects[participant_id]:
                    # need to be set in the beginning because we want to have 0 values
                    # if facility counts (e.g. food place counts)
                    # #=surrounding that map object (e.g. a happy place) is 0
                    facility_count = {f: 0 for f in facilities}

                    coord1 = obj.coordinates[0]

                    for facility_id in facility_dict:
                        type = facility_dict[facility_id][0]
                        coord2 = facility_dict[facility_id][1]

                        distance = self._calculate_haversine([coord1, coord2])
                        if distance <= 500:
                            facility_count[type] = facility_count[type] + 1

                    # we need to know facility counts for each marked place, e.g. happy place
                    for type in facility_count:
                        vals = total_facility_count.setdefault(type, [])
                        vals.append(facility_count[type])

        for group in total_facility_count_by_group:
            logging.info(f"{group}")
            total_facility_count = total_facility_count_by_group[group]

            for type in total_facility_count:
                vals = total_facility_count[type]

                logging.info(f"{type},{round(numpy.average(vals),2)},{round(numpy.std(vals),2)},"
                             f"{round(numpy.min(vals),2)},{round(numpy.max(vals),2)}")


    def calculate_facilities_around_map_obj(self,poi_file,obj_idx):
        facilities, facility_dict = self._get_facilities(poi_file)
        participant2objects = self._get_participant2objects_dict(obj_idx)

        total_facility_count = {}

        participant_count = 0
        for participant_id in participant2objects:
            participant_count += 1


            #logging.info(f"Processing participant {participant_count} out of {len(participant2objects)}")
            #for each marked place, e.g. happy place
            for obj in participant2objects[participant_id]:
                # need to be set in the beginning because we want to have 0 values
                # if facility counts for that facility is 0
                facility_count = {f:0 for f in facilities}

                coord1 = obj.coordinates[0]

                for facility_id in facility_dict:
                    type = facility_dict[facility_id][0]
                    coord2 = facility_dict[facility_id][1]

                    distance = self._calculate_haversine([coord1, coord2])
                    if distance <= 500:
                        facility_count[type] = facility_count[type] + 1

                # we need to know facility counts for each marked place, e.g. happy place
                for type in facility_count:
                    vals = total_facility_count.setdefault(type,[])
                    vals.append(facility_count[type])

        for type in total_facility_count:
            vals = total_facility_count[type]

            logging.info(f"{type},{round(numpy.average(vals),2)},{round(numpy.std(vals),2)},"
                         f"{round(numpy.min(vals),2)},{round(numpy.max(vals),2)}")

    def count_obj(self, obj_idx):
        participant2objects = self._get_participant2objects_dict(obj_idx)

        counts = []
        for participant_id in participant2objects:
            objs = participant2objects[participant_id]
            counts.append(len(objs))

        not_answering = [id for id in self.participants.keys()
                         if id not in participant2objects.keys()]
        answering = [id for id in self.participants.keys() if id in participant2objects.keys()]

        logging.info(f"not answering, answering, total, avg, std, min, max")
        logging.info(f"{len(not_answering)}({round(len(not_answering)/len(self.participants.keys()),2)}),"
                     f"{len(answering)}({round(len(answering)/len(self.participants.keys()),2)}),"
                     f"{sum(counts)},{round(numpy.average(counts),2)},{round(numpy.std(counts),2)},"
                     f"{min(counts)},{max(counts)}")

    # param @attribute is the continuous or ordinal values that belong to obj @obj_idx
    # this method returns basic statistics of each variable group (e.g. age group)
    def calculate_basic_stats(self, obj_idx, attribute):
        scores = self._get_scores(obj_idx, attribute)

        did_not_answer = sum(math.isnan(x) for x in scores)
        answers = len(scores) - did_not_answer

        boxvalues = descriptive_stat.calculate_boxplot(list(filter(lambda x: not math.isnan(x), scores)))

        logging.info(f"{answers},{did_not_answer},{boxvalues}")

    # param @attribute is the continuous or ordinal values that belong to obj @obj_idx
    # this method calculates the count/percentage of nominal values (1, 2, 3, 4, 5)
    def calculate_nominal_counts(self, obj_idx, attribute):
        nomstats = self._get_nominal_values(obj_idx, attribute)

        summary_stat = [(x, nomstats[x], round(nomstats[x]/sum(nomstats.values()),2)) for x in nomstats.keys()]

        logging.info(sum(nomstats.values()))
        logging.info(summary_stat)

    # param @attribute is the continuous or ordinal values that belong to obj @obj_idx
    # this method calculates the count/percentage of nominal values (1/2, 3, 4/5)
    def calculate_grouped_nominal_counts(self, obj_idx, attribute):
        scores = self._get_scores(obj_idx, attribute)

        did_not_answer = sum(math.isnan(x) for x in scores)

        low = len(list(filter(lambda x: x == 1.0 or x == 2.0, scores)))
        neu = len(list(filter(lambda x: x == 3.0, scores)))
        hig = len(list(filter(lambda x: x == 4.0 or x == 5.0, scores)))

        total = (did_not_answer + low + neu + hig) * 1.0

        logging.info("did not answer, low, neutral, high")
        logging.info(f"{did_not_answer}({round(did_not_answer/total,2)}),{low}({round(low/total,2)}),{neu}({round(neu/total,2)}), {hig}({round(hig/total,2)})")

    def calculate_word_counts_from_sent_by_mapobjattr(self, groupobj_idx, group_attr, mapobj_idx, mapobj_attr):
        # participant-house_objects
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        group2sentences = {}

        for participant_id in participant2groupobjects:
            group_objs = participant2groupobjects[participant_id]

            # get the group of participant "participant_id"
            group = self._get_mapobj_attr_value(group_objs, group_attr)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                text = ""
                for obj in objs:
                    raw = getattr(obj, mapobj_attr)

                    if isinstance(raw, str):
                        text += descriptive_stat.basic_preprocess_text(raw)

                sentences = group2sentences.setdefault(group, [])
                sentences.append(text)

        for group in group2sentences:
            sentences = group2sentences[group]
            sorted_word, sorted_adj, sorted_noun = descriptive_stat.rank_word_in_sentences(sentences)

            logging.info(f"{group}")
            logging.info(f"{sorted_word}")
            # logging.info(f"{sorted_adj}")
            # logging.info(f"{sorted_noun}")

    def calculate_word_counts_from_sent_by_pardata (self, pardata_idx, mapobj_idx, attribute):
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        group2sentences = {}

        for participant_id in self.participants:
            group = self.participants[participant_id].data[pardata_idx]

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                text = ""
                for obj in objs:
                    raw = getattr(obj, attribute)
                    if isinstance(raw,str):
                        text += descriptive_stat.basic_preprocess_text(raw)

                sentences = group2sentences.setdefault(group, [])
                sentences.append(text)

        for group in group2sentences:
            sentences = group2sentences[group]
            sorted_word, sorted_adj, sorted_noun = descriptive_stat.rank_word_in_sentences(sentences)

            logging.info(f"{group}")
            logging.info(f"{sorted_word}")
            # logging.info(f"{sorted_adj}")
            # logging.info(f"{sorted_noun}")

    def calculate_nominal_counts_by_pardata(self, pardata_idx, mapobj_idx, attribute):
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        group2nomvals = {}

        for participant_id in self.participants:
            group = self.participants[participant_id].data[pardata_idx]

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                nom_val = ""
                for obj in objs:
                    raw = getattr(obj, attribute)
                    if isinstance(raw, str):
                        nom_val = raw

                    nomvals = group2nomvals.setdefault(group, {})
                    nomvals[nom_val] = nomvals.setdefault(nom_val, 0) + 1

        for group in group2nomvals:
            nomstats = group2nomvals[group]
            summary_stat = [(x, nomstats[x], round(nomstats[x] / sum(nomstats.values()), 2)) for x in nomstats.keys()]
            logging.info(f"{group},{summary_stat}")


    def calculate_nominal_counts_by_region(self, regobj_idx, mapobj_idx, attribute):
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        reg2nomvals = {}

        for participant_id in participant2regobjects:
            regobjects = participant2regobjects[participant_id]
            # get the region of participant "participant_id"
            region = self._get_region_given_regobjects(regobjects)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                nom_val = ""
                for obj in objs:
                    raw = getattr(obj, attribute)
                    if isinstance(raw, str):
                        nom_val = raw

                    nomvals = reg2nomvals.setdefault(region, {})
                    nomvals[nom_val] = nomvals.setdefault(nom_val,0) + 1

        for region in reg2nomvals:
            nomstats = reg2nomvals[region]
            summary_stat = [(x, nomstats[x], round(nomstats[x] / sum(nomstats.values()), 2)) for x in nomstats.keys()]
            logging.info(f"{region},{summary_stat}")

    def calculate_word_counts_from_sent_by_region (self, regobj_idx, mapobj_idx, attribute):
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        reg2sentences = {}

        for participant_id in participant2regobjects:
            regobjects = participant2regobjects[participant_id]
            #get the region of participant "participant_id"
            region = self._get_region_given_regobjects(regobjects)

            if participant_id in participant2mapobjects:
                objs = participant2mapobjects[participant_id]

                text = ""
                for obj in objs:
                    raw = getattr(obj, attribute)
                    if isinstance(raw, str):
                        text += descriptive_stat.basic_preprocess_text(raw)

                sentences = reg2sentences.setdefault(region,[])
                sentences.append(text)

        for reg in reg2sentences:
            sentences = reg2sentences[reg]
            sorted_word, sorted_adj, sorted_noun = descriptive_stat.rank_word_in_sentences(sentences)

            logging.info(f"{reg}")
            logging.info(f"{sorted_word}")
            #logging.info(f"{sorted_adj}")
            #logging.info(f"{sorted_noun}")

    #this method calculate top 10 word counts of answers to
    #a pop-up question of mapping objects
    #this method has two parameters, the object index, and the attribute of the object
    #it calculates word counts of the "attribute" of object "obj_idx"
    def calculate_word_counts_from_sent(self, obj_idx, attribute):
        participant2objects = self._get_participant2objects_dict(obj_idx)

        sentences = []
        for participant_id in participant2objects:
            objs = participant2objects[participant_id]
            for obj in objs:
                text = ""

                t = getattr(obj, attribute)
                if isinstance(t, str):
                    text = descriptive_stat.basic_preprocess_text(t)

                sentences.append(text)

        sorted_word, sorted_adj, sorted_noun = descriptive_stat.rank_word_in_sentences(sentences)

        logging.info(f"{sorted_word}")
        logging.info(f"{sorted_adj}")
        logging.info(f"{sorted_noun}")

    # data_col_idx is the participant data you want to calculate basic statistics on
    # obj_idx refers to the index of the obj_arr you initate in obj_arrs
    # the obj_arr refers to the objects whose region you need, for e.g. house
    def calculate_participant_stats_by_region(self, obj_idx, data_col_idx):
        region2vals = self._get_region2vals(obj_idx, data_col_idx)

        for region in region2vals:
            scores = region2vals[region]
            did_not_answer = sum(math.isnan(x) for x in scores)
            answers = len(scores) - did_not_answer

            answered = list(filter(lambda x: not math.isnan(x), scores))
            boxvalues = []
            if len(answered) > 0:
                boxvalues = descriptive_stat.calculate_boxplot(answered)

            logging.info(f"{region},{answers},{did_not_answer},{boxvalues}")

    def calculate_route_coincidences_by_mapobjattr(self, obj_arr_idx1, obj_arr_idx2, groupobj_idx, grouping_attr):
        participant2routeobjs1 = self._get_participant2objects_dict(obj_arr_idx1)
        participant2routeobjs2 = self._get_participant2objects_dict(obj_arr_idx2)
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)

        group2coincidences = {}

        for participant_id in participant2groupobjects:
            if participant_id in participant2routeobjs1:
                if participant_id in participant2routeobjs2:
                    routeobjs1 = participant2routeobjs1[participant_id]
                    routeobjs2 = participant2routeobjs2[participant_id]

                    groupobjs = participant2groupobjects[participant_id]
                    group = self._get_mapobj_attr_value(groupobjs, grouping_attr)

                    for routeobj1 in routeobjs1:
                        for routeobj2 in routeobjs2:
                            route1 = getattr(routeobj1, "coordinates")
                            route2 = getattr(routeobj2, "coordinates")

                            # find distance coincided for each route pair
                            distance_coincided = self.calculate_distance_coincided_between_routes(route1, route2)

                            distance_coincidences = group2coincidences.setdefault(group, [])
                            distance_coincidences.append(distance_coincided)

        logging.info("total,mean,std,mean,max")
        for group in group2coincidences:
            c = group2coincidences[group]
            logging.info(f"{group},{len(c)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_point_route_coincidences_by_mapobjattr(self, route_obj_idx, place_idx, groupobj_idx, grouping_attr):
        participant2distances = self.caculate_distance_between_point_route_mapping_objects(route_obj_idx, place_idx)
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)

        group2coincidences = {}

        for participant_id in participant2groupobjects:
            if participant_id in participant2distances:
                groupobjs = participant2groupobjects[participant_id]
                group = self._get_mapobj_attr_value(groupobjs, grouping_attr)

                distances = participant2distances[participant_id]
                c = [x for x in distances if x < 83]
                group2coincidences.setdefault(group, []).append(len(c))

        logging.info("total,mean,std,mean,max")
        for group in group2coincidences:
            c = group2coincidences[group]
            logging.info(f"{group},{round(sum(c),2)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_place_coincidences_by_mapobjattr(self, obj_arr_idx1, obj_arr_idx2, groupobj_idx, grouping_attr):
        participant2distances = self.calculate_distance_between_point_mapping_objects(obj_arr_idx1, obj_arr_idx2)

        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)

        group2coincidences = {}

        for participant_id in participant2groupobjects:
            if participant_id in participant2distances:
                groupobjs = participant2groupobjects[participant_id]
                group = self._get_mapobj_attr_value(groupobjs, grouping_attr)

                distances = participant2distances[participant_id]
                c = [x for x in distances if x < 83]
                group2coincidences.setdefault(group, []).append(len(c))

        logging.info("total,mean,std,mean,max")
        for group in group2coincidences:
            c = group2coincidences[group]
            logging.info(f"{group},{round(sum(c),2)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_place_coincidences_by_pardata(self, obj_arr_idx1, obj_arr_idx2, pardata_idx):

        participant2distances = self.calculate_distance_between_point_mapping_objects(obj_arr_idx1, obj_arr_idx2)

        group2coincidences = {}

        for participant_id in self.participants:
            if participant_id in participant2distances:
                group = self.participants[participant_id].data[pardata_idx]

                distances = participant2distances[participant_id]
                c = [x for x in distances if x < 83]
                group2coincidences.setdefault(group, []).append(len(c))

        logging.info("total,mean,std,mean,max")
        for group in group2coincidences:
            c = group2coincidences[group]
            logging.info(f"{group},{round(sum(c),2)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_route_coincidences_by_pardata(self, route_obj_1_idx, route_obj_2_idx, pardata_idx):
        participant2routeobjs1 = self._get_participant2objects_dict(route_obj_1_idx)
        participant2routeobjs2 = self._get_participant2objects_dict(route_obj_2_idx)

        group2coincidences = {}

        for participant_id in participant2routeobjs1:
            if participant_id in participant2routeobjs2:
                routeobjs1 = participant2routeobjs1[participant_id]
                routeobjs2 = participant2routeobjs2[participant_id]

                group = self.participants[participant_id].data[pardata_idx]

                for routeobj1 in routeobjs1:
                    for routeobj2 in routeobjs2:
                        route1 = getattr(routeobj1, "coordinates")
                        route2 = getattr(routeobj2, "coordinates")

                        # find distance coincided for each route pair
                        distance_coincided = self.calculate_distance_coincided_between_routes(route1, route2)

                        distance_coincidences = group2coincidences.setdefault(group, [])
                        distance_coincidences.append(distance_coincided)

        logging.info("total,mean,std,mean,max")
        for group in group2coincidences:
            c = group2coincidences[group]
            logging.info(f"{group},{len(c)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_route_coincidences_by_region(self, route_obj_1_idx, route_obj_2_idx, regobj_idx):
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)

        participant2routeobjs1 = self._get_participant2objects_dict(route_obj_1_idx)
        participant2routeobjs2 = self._get_participant2objects_dict(route_obj_2_idx)

        region2coincidences = {}

        # counter = 0
        for participant_id in participant2routeobjs1:
            # counter += 1

            if participant_id in participant2routeobjs2:
                routeobjs1 = participant2routeobjs1[participant_id]
                routeobjs2 = participant2routeobjs2[participant_id]

                regobjects = participant2regobjects[participant_id]
                # get the region of participant "participant_id"
                region = self._get_region_given_regobjects(regobjects)

                for routeobj1 in routeobjs1:
                    for routeobj2 in routeobjs2:
                        route1 = getattr(routeobj1, "coordinates")
                        route2 = getattr(routeobj2, "coordinates")

                        # find distance coincided for each route pair
                        distance_coincided = self.calculate_distance_coincided_between_routes(route1, route2)

                        distance_coincidences = region2coincidences.setdefault(region, [])
                        distance_coincidences.append(distance_coincided)

        logging.info("total,mean,std,mean,max")
        for reg in region2coincidences:
            c = region2coincidences[reg]
            logging.info(f"{reg},{len(c)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_place_coincidences_by_region(self, obj_arr_idx1, obj_arr_idx2, regobj_idx):
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        participant2distances = self.calculate_distance_between_point_mapping_objects(obj_arr_idx1, obj_arr_idx2)

        region2coincidences = {}

        for participant_id in participant2regobjects:
            if participant_id in participant2distances:
                regobjects = participant2regobjects[participant_id]
                # get the region of participant "participant_id"
                region = self._get_region_given_regobjects(regobjects)

                distances = participant2distances[participant_id]
                c = [x for x in distances if x < 83]
                region2coincidences.setdefault(region,[]).append(len(c))

        logging.info("total,mean,std,mean,max")
        for reg in region2coincidences:
            c = region2coincidences[reg]
            logging.info(f"{reg},{round(sum(c),2)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_point_route_coincidences_by_pardata(self, route_obj_idx, place_idx, pardata_idx):
        participant2distances = self.caculate_distance_between_point_route_mapping_objects(route_obj_idx, place_idx)

        group2coincidences = {}

        for participant_id in self.participants:
            if participant_id in participant2distances:
                group = self.participants[participant_id].data[pardata_idx]

                distances = participant2distances[participant_id]
                c = [x for x in distances if x < 83]
                group2coincidences.setdefault(group, []).append(len(c))

        logging.info("total,mean,std,mean,max")
        for group in group2coincidences:
            c = group2coincidences[group]
            logging.info(f"{group},{round(sum(c),2)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_point_route_coincidences_by_region(self, route_obj_idx, place_idx, regobj_idx):
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        participant2distances = self.caculate_distance_between_point_route_mapping_objects(route_obj_idx, place_idx)

        region2coincidences = {}

        for participant_id in participant2regobjects:
            if participant_id in participant2distances:
                regobjects = participant2regobjects[participant_id]
                # get the region of participant "participant_id"
                region = self._get_region_given_regobjects(regobjects)

                distances = participant2distances[participant_id]
                c = [x for x in distances if x < 83]
                region2coincidences.setdefault(region, []).append(len(c))

        logging.info("total,mean,std,mean,max")
        for reg in region2coincidences:
            c = region2coincidences[reg]
            logging.info(f"{reg},{round(sum(c),2)},{round(numpy.average(c),2)},"
                         f"{round(numpy.std(c),2)},{round(numpy.min(c),2)},{round(numpy.max(c),2)}")

    def calculate_point_route_coincidences(self, route_obj_idx, place_idx):
        participant2distances = self.caculate_distance_between_point_route_mapping_objects(route_obj_idx, place_idx)

        coincidences = []
        for participant_id in participant2distances:
            distances = participant2distances[participant_id]

            # if distance less than 83 m, it's a coincidence,
            # referring to finger pointing error
            c = [x for x in distances if x < 83]

            coincidences.append(len(c))

        logging.info(f"{sum(coincidences)}, {round(numpy.average(coincidences),2)}, {round(numpy.std(coincidences),2)},"
                     f"{min(coincidences)}, {max(coincidences)}")

    # find distance coincided
    # of possible route pairs of a participant
    # this is to be done for all participants
    def calculate_route_coincidences(self, route_obj_1_idx, route_obj_2_idx):
        participant2routeobjs1 = self._get_participant2objects_dict(route_obj_1_idx)
        participant2routeobjs2 = self._get_participant2objects_dict(route_obj_2_idx)

        # each route coincidence item tells you the distance the two routes coincide
        distance_coincidences = []


        #counter = 0
        for participant_id in participant2routeobjs1:
            #counter += 1

            if participant_id in participant2routeobjs2:
                routeobjs1 = participant2routeobjs1[participant_id]
                routeobjs2 = participant2routeobjs2[participant_id]

                for routeobj1 in routeobjs1:
                    for routeobj2 in routeobjs2:
                        route1 = getattr(routeobj1,"coordinates")
                        route2 = getattr(routeobj2,"coordinates")

                        # find distance coincided for each route pair
                        distance_coincided = self.calculate_distance_coincided_between_routes(route1, route2)
                        distance_coincidences.append(distance_coincided)

                        '''if counter >=1 and counter <=10 and distance_coincided > 0:
                            m1 = folium.Map(location=[1.348919, 103.948600], zoom_start=14, tiles="cartodbpositron")
                            folium.PolyLine([[x[1], x[0]] for x in route1], color="green", weight=1.5, opacity=1).add_to(m1)
                            folium.PolyLine([[x[1], x[0]] for x in route2], color="black", weight=1.5, opacity=1).add_to(m1)

                            print(counter, distance_coincided, route1, route2)
                            m1.save(f"participant{counter}_{round(distance_coincided,2)}.html")'''

        logging.info(f"{len(distance_coincidences)}, {round(numpy.average(distance_coincidences),2)}, {round(numpy.std(distance_coincidences),2)},"
                     f"{min(distance_coincidences)}, {max(distance_coincidences)}")


    # find a list of coincidences of locations of two objects belonging to the same participant
    # do this for all participants
    def calculate_place_coincidences(self, obj_arr_idx1, obj_arr_idx2):
        participant2distances = self.calculate_distance_between_point_mapping_objects(obj_arr_idx1, obj_arr_idx2)

        coincidences = []
        for participant_id in participant2distances:
            distances = participant2distances[participant_id]

            # if distance less than 83 m, it's a coincidence,
            # referring to finger pointing error
            c = [x for x in distances if x < 83]

            coincidences.append(len(c))

        logging.info(f"{sum(coincidences)}, {round(numpy.average(coincidences),2)}, {round(numpy.std(coincidences),2)},"
                     f"{min(coincidences)}, {max(coincidences)}")

    def calculate_distance_coincided_between_lines(self,line1,line2):
        distance_coincided = 0
        coincided_end_points = []

        for point in line1:
            proj, dist = self._calculate_shortest_distance_of_point_to_line(point, line2)
            # points coincided with route if projected distance to the line is < 83
            if dist > 0 and dist < 83:
                coincided_end_points.append(proj)

        # if coincidence points consists of one point in line 1, one point in line 2
        # meaning 1 point in line 1 has < 83 projected distance to line 2
        # and 1 point in line 2 has < 83 projected distance to line 1
        while len(coincided_end_points) < 2:
            for point in line2:
                proj, dist = self._calculate_shortest_distance_of_point_to_line(point, line1)
                if dist > 0 and dist < 83:
                    # add the point, not the projection point
                    # because you need the distance between projected point 1 to line 2
                    # and a point in line 2
                    coincided_end_points.append(point)
                    break
            break

        # if there are two points that are close to each other
        # means the routes coincided, because we only deal with straight lines
        if len(coincided_end_points) > 1:
            distance_coincided = self._calculate_haversine(coincided_end_points)

        return distance_coincided

    def calculate_distance_of_point_to_route(self, route, place_coordinate):
        distances = []

        #if the route is a point
        if len(route) == 1:
            distance = self._calculate_haversine([place_coordinate, route[0]])
            distances.append(distance)
        else:
            # for each line segment in a route
            for i in range(0, len(route) - 1):
                # line consists of two sequential points in a route
                line_of_route = [route[i], route[i + 1]]
                proj, distance = self._calculate_shortest_distance_of_point_to_line(place_coordinate, line_of_route)

                if distance < 0:
                    # no perpendicular projection between the line, and the route
                    distance = min(self._calculate_haversine([place_coordinate, line_of_route[0]]),
                                self._calculate_haversine([place_coordinate, line_of_route[1]]))

                distances.append(distance)

        # minimum distance of a point to a line segment of a route is
        # the distance of the point to that route
        return min(distances)

    # this method calculates total distance coincided between two routes
    def calculate_distance_coincided_between_routes(self, route1, route2):
        distance = 0

        # coincided distance between routes is equal to
        # total coincided distance between line segments of the route
        # this for loop will not run, if the route is only a single point
        for i in range(0, len(route1) - 1):
            # line consists of two sequential points in a route
            line_of_route1 = [route1[i], route1[i+1]]

            for j in range(0, len(route2) - 1):
                line_of_route2 = [route2[j], route2[j + 1]]

                increment = self.calculate_distance_coincided_between_lines(line_of_route1, line_of_route2)
                distance += increment

        return distance

    def caculate_distance_between_point_route_mapping_objects(self, route_idx, place_idx):
        participant2route_obj = self._get_participant2objects_dict(route_idx)
        participant2place_obj = self._get_participant2objects_dict(place_idx)

        participant2distances = {}

        for participant_id in self.participants:
            distances = []

            if participant_id in participant2route_obj and participant_id in participant2place_obj:
                for obj1 in participant2route_obj[participant_id]:
                    route_coordinates = getattr(obj1, "coordinates")

                    for obj2 in participant2place_obj[participant_id]:
                        place_coordinate = getattr(obj2, "coordinates")[0]

                        distance = self.calculate_distance_of_point_to_route(route_coordinates, place_coordinate)

                        distances.append(distance)

            participant2distances[participant_id] = distances

        return participant2distances

    # this method calculate distance between mapping objects that belong to the same participants
    # in other words, distance between mapping objects of different participants is not calculated
    def calculate_distance_between_point_mapping_objects(self, obj_arr_idx1, obj_arr_idx2):
        participant2objs1 = self._get_participant2objects_dict(obj_arr_idx1)
        participant2objs2 = self._get_participant2objects_dict(obj_arr_idx2)

        participant2distances = {}

        for participant_id in self.participants:
            distances = []

            if participant_id in participant2objs1 and participant_id in participant2objs2:
                for obj1 in participant2objs1[participant_id]:
                    coordinate1 = getattr(obj1, "coordinates")[0]

                    for obj2 in participant2objs2[participant_id]:
                        coordinate2 = getattr(obj2, "coordinates")[0]

                        distance = self._calculate_haversine([coordinate1, coordinate2])
                        distances.append(distance)

            participant2distances[participant_id] = distances

        return participant2distances



    # data_idcs indicate which attributes specific to respondents, e.g. gender, age are required
    # these attributes are not related to mapping objects
    # mapobj_idcs, & mapobj_attrs indicate which attributes of which mapobjs are required
    def merge_mapobj_into_table(self, data_idcs, mapobj_idcs, mapobj_attrs):
        tabl = pd.DataFrame([])

        for participant_id in self.participants:
            # each participant represents a rown
            row = [participant_id]

            # add each participant attribute into each column
            for data_id in data_idcs:
                row.append(self.participants[participant_id].data[data_id])

            # add each mapobject attribute into each column
            for i in range(0, len(mapobj_idcs)):
                idx = mapobj_idcs[i]
                participant2mapobjects = self._get_participant2objects_dict(idx)

                if participant_id in participant2mapobjects:
                    mapobjs = participant2mapobjects[participant_id]

                    attrs = set([])
                    # if there are more than 1 mapobj, combine the values of the mapobj
                    for obj in mapobjs:
                        # get the attribute
                        attr = getattr(obj, mapobj_attrs[i])

                        if "coordinates" == mapobj_attrs[i]:
                            for coordinate in attr:
                                region = self._get_region_from_coord(coordinate[1], coordinate[0])
                                attrs.add(region)
                        else:
                            # convert to str, so that nan is also converted to a valid str value
                            attrs.add(str(attr))

                    cell_value = "; ".join(sorted(list(attrs)))
                    row.append(cell_value)
                else:
                    # no map object created for this participant
                    # he does not fill in anything
                    row.append("")

            tabl = tabl.append([row])
            # check, whether those without unhappy places is the right respondents

        tabl.to_csv("map_obj_summary.csv")

    def _plot_routes_given_group(self, group2routes):
        for group in group2routes:
            m1 = folium.Map(location=[1.348919, 103.948600], zoom_start=14, tiles="cartodbpositron")

            if group in self.tampines_poly:
                for boundary in self.tampines_poly[group]:
                    mod_boundary = [[x[1],x[0]] for x in boundary]
                    mod_boundary.append(mod_boundary[0])
                    folium.PolyLine(mod_boundary, color="black", weight=1.5, dash_array='3', opacity=1).add_to(m1)
            else:
                for g in self.tampines_poly:
                    for boundary in self.tampines_poly[g]:
                        mod_boundary = [[x[1], x[0]] for x in boundary]
                        mod_boundary.append(mod_boundary[0])
                        folium.PolyLine(mod_boundary, color="black", weight=1.5, dash_array='3', opacity=1).add_to(m1)

            for coordinates in group2routes[group]:
                route = [[x[1], x[0]] for x in coordinates]
                folium.PolyLine(route, color="green", weight=0.75, opacity=1).add_to(m1)

            group = group.replace("/","_")
            group = group.replace(":","_")
            m1.save(f"{group}.html")

    def _plot_coordinates_given_group(self, group2coordinates):
        for group in group2coordinates:
            m1 = folium.Map(location=[1.348919, 103.948600], zoom_start=14, tiles="cartodbpositron")

            if group in self.tampines_poly:
                for boundary in self.tampines_poly[group]:
                    mod_boundary = [[x[1],x[0]] for x in boundary]
                    mod_boundary.append(mod_boundary[0])
                    folium.PolyLine(mod_boundary, color="black", weight=0.75, dash_array='3', opacity=1).add_to(m1)
            else:
                for g in self.tampines_poly:
                    for boundary in self.tampines_poly[g]:
                        mod_boundary = [[x[1], x[0]] for x in boundary]
                        mod_boundary.append(mod_boundary[0])
                        folium.PolyLine(mod_boundary, color="black", weight=0.75, dash_array='3', opacity=1).add_to(m1)

            for coordinate in group2coordinates[group]:
                folium.CircleMarker(location=[coordinate[1], coordinate[0]], radius=1,
                                    fill_color="blue", color="blue",
                                    fill=True, fill_opacity=0.7).add_to(m1)

            group = group.replace("/","_")
            group = group.replace(":","_")
            m1.save(f"{group}.html")

    def plot_route_by_mapobjattr(self, groupobj_idx, group_attr, mapobj_idx):
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)
        # participant-group_objects
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)

        group2coordinates = {}

        for participant_id in participant2groupobjects:
            # participant answers the question and thus has the map objects
            if participant_id in participant2mapobjects:
                map_objs = participant2mapobjects[participant_id]
                map_objs_coordinates = []

                for map_obj in map_objs:
                    coordinates = getattr(map_obj, "coordinates")
                    map_objs_coordinates.append(coordinates)

                # get the group of participant "participant_id"
                group_objs = participant2groupobjects[participant_id]
                group = self._get_mapobj_attr_value(group_objs, group_attr)

                coordinates = group2coordinates.setdefault(group, [])
                coordinates.extend(map_objs_coordinates)

        self._plot_routes_given_group(group2coordinates)


    def create_plot_by_mapobjattr(self, groupobj_idx, group_attr, mapobj_idx):
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)
        # participant-group_objects
        participant2groupobjects = self._get_participant2objects_dict(groupobj_idx)

        group2coordinates = {}

        for participant_id in participant2groupobjects:
            # participant answers the question and thus has the map objects
            if participant_id in participant2mapobjects:
                map_objs = participant2mapobjects[participant_id]
                map_objs_coordinates = []

                for map_obj in map_objs:
                    coordinate = getattr(map_obj, "coordinates")[0]
                    map_objs_coordinates.append(coordinate)

                group_objs = participant2groupobjects[participant_id]
                group = self._get_mapobj_attr_value(group_objs, group_attr)

                coordinates = group2coordinates.setdefault(group, [])
                coordinates.extend(map_objs_coordinates)

        self._plot_coordinates_given_group(group2coordinates)

    def create_plot_by_pardata(self, pardata_idx, mapobj_idx):
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        group2coordinates = {}

        for participant_id in self.participants:
            # participant answers the question and thus has the map objects
            if participant_id in participant2mapobjects:
                map_objs = participant2mapobjects[participant_id]
                map_objs_coordinates = []

                for map_obj in map_objs:
                    coordinate = getattr(map_obj, "coordinates")[0]
                    map_objs_coordinates.append(coordinate)

                group = self.participants[participant_id].data[pardata_idx]

                coordinates = group2coordinates.setdefault(group, [])
                coordinates.extend(map_objs_coordinates)

        self._plot_coordinates_given_group(group2coordinates)

    def plot_route_by_pardata(self, pardata_idx, mapobj_idx):
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        group2coordinates = {}

        for participant_id in self.participants:
            # participant answers the question and thus has the map objects
            if participant_id in participant2mapobjects:
                map_objs = participant2mapobjects[participant_id]
                map_objs_coordinates = []

                for map_obj in map_objs:
                    coordinates = getattr(map_obj, "coordinates")
                    map_objs_coordinates.append(coordinates)

                # get the group of participant "participant_id"
                group = self.participants[participant_id].data[pardata_idx]

                coordinates = group2coordinates.setdefault(group, [])
                coordinates.extend(map_objs_coordinates)

        self._plot_routes_given_group(group2coordinates)


    def plot_route_by_region(self, regobj_idx, mapobj_idx):
        # participant-house_objects
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        region_to_coordinates = {}

        for participant_id in participant2regobjects:
            # participant answers the question and thus has the map objects
            if participant_id in participant2mapobjects:
                map_objs = participant2mapobjects[participant_id]
                map_objs_coordinates = []

                for map_obj in map_objs:
                    coordinates = getattr(map_obj, "coordinates")
                    map_objs_coordinates.append(coordinates)

                regobjects = participant2regobjects[participant_id]

                # get the region of participant "participant_id"
                region = self._get_region_given_regobjects(regobjects)

                coordinates = region_to_coordinates.setdefault(region, [])
                coordinates.extend(map_objs_coordinates)

        self._plot_routes_given_group(region_to_coordinates)

    def create_plot_by_region(self, regobj_idx, mapobj_idx):
        # participant-house_objects
        participant2regobjects = self._get_participant2objects_dict(regobj_idx)
        # participant-map_objects
        participant2mapobjects = self._get_participant2objects_dict(mapobj_idx)

        region_to_coordinates = {}

        for participant_id in participant2regobjects:
            # participant answers the question and thus has the map objects
            if participant_id in participant2mapobjects:
                map_objs = participant2mapobjects[participant_id]
                map_objs_coordinates = []

                for map_obj in map_objs:
                    coordinate = getattr(map_obj, "coordinates")[0]
                    map_objs_coordinates.append(coordinate)

                regobjects = participant2regobjects[participant_id]

                # get the region of participant "participant_id"
                region = self._get_region_given_regobjects(regobjects)

                coordinates = region_to_coordinates.setdefault(region, [])
                coordinates.extend(map_objs_coordinates)

        self._plot_coordinates_given_group(region_to_coordinates)


    def plot_route(self, obj_arr_indices, obj_arr_names):
        m1 = folium.Map(location=[1.348919, 103.948600], zoom_start=14, tiles="cartodbpositron")

        for idx in obj_arr_indices:
            objs = self.obj_arrs[idx]

            for obj in objs:
                if obj.respondent_id in self.participants:
                    coordinates = obj.coordinates
                    route = [[x[1], x[0]] for x in coordinates]
                    folium.PolyLine(route, color="green", weight=0.75, opacity=1).add_to(m1)

            m1.save(f"{obj_arr_names[idx]}.html")

    def create_plot(self, obj_arr_indices, obj_arr_names):
        m1 = folium.Map(location=[1.348919, 103.948600], zoom_start=14, tiles="cartodbpositron")

        for idx in obj_arr_indices:
            objs = self.obj_arrs[idx]

            for obj in objs:
                if obj.respondent_id in self.participants:
                    coordinates = obj.coordinates
                    for coordinate in coordinates:
                        folium.CircleMarker(location=[coordinate[1], coordinate[0]], radius=1,
                                            fill_color="blue", color="blue",
                                            fill=True, fill_opacity=0.7).add_to(m1)

            m1.save(f"{obj_arr_names[idx]}.html")



    # obj_arr_indices specify which list of objects you want to perform
    # this method on.
    # obj_arr_names specify what name to save the result of the method
    # performed on the list of obj specified by the idx.
    # filename will carry .html automatically.
    def create_plot_by_age(self, obj_arr_indices, obj_arr_names):
        m1 = folium.Map(location=[1.348919, 103.948600], zoom_start=14, tiles="cartodbpositron")

        for idx in obj_arr_indices:
            objs = self.obj_arrs[idx]
            colors = {}

            for obj in objs:
                age_group = self.participants.get(obj.respondent_id).age_group

                c = colors.setdefault(age_group, get_random_colors(1)[0])

                folium.CircleMarker(location=[obj.lat, obj.long],radius = 4,
                                    fill_color = c, color = c,
                                    fill=True, fill_opacity=0.7, tooltip=age_group).add_to(m1)

            m1.save(f"{obj_arr_names[idx]}.html")

            # you may create nominal legends

def generate_impro_suggestion(filename):
    df = pd.read_csv(filename)
    logging.info(len(df))

    for i in range(5, len(df.columns)-1):
        subdf = df[df.iloc[:, i] == 1]
        sugg = []
        # if not empty. Some of the environment barriers are empty, hypothetical e.g.
        # no one raises issues about lack of greeneries
        if len(subdf) > 0:
            sugg = [x for x in subdf.iloc[:,len(subdf.columns)-1]]

        logging.info(sugg)


# generate summary distribution of different environmental barriers/improvement suggestions
def generate_summary_distribution(filename):
    df = pd.read_csv(filename)
    logging.info(len(df))

    for i in range(5, len(df.columns)):
        subdf = df[df.iloc[:,i] == 1]

        loc = []
        for d in list(subdf.iloc[:,3]):
            loc.extend(d.split("; "))

        age = []
        for d in list(subdf.iloc[:, 2]):
            age.extend(d.split("; "))

        gender = []
        for d in list(subdf.iloc[:, 1]):
            gender.extend(d.split("; "))

        total_participants = len(subdf)
        loc_dist = [(g[0], round(len(list(g[1]))*1.0/total_participants,2)) for g in itertools.groupby(sorted(loc))]
        loc_dist = sorted(loc_dist, key=lambda x:x[1], reverse=True)
        age_dist = [(g[0], round(len(list(g[1]))*1.0/total_participants,2)) for g in itertools.groupby(sorted(age))]
        age_dist = sorted(age_dist, key=lambda x: x[1], reverse=True)
        gender_dist = [(g[0], round(len(list(g[1]))*1.0/total_participants,2)) for g in itertools.groupby(sorted(gender))]
        gender_dist = sorted(gender_dist, key=lambda x: x[1], reverse=True)

        logging.info(f"{total_participants},{loc_dist},{age_dist},{gender_dist}")

def get_random_colors(num_color):
    colors = []
    r = lambda: random.randint(0, 255)
    for o in range(num_color):
        colors.append(f'#%02X%02X%02X' % (r(), r(), r()))
    return colors

#mapping = Mapping(["data/house.csv"],["House"], "data/data.csv")

#---participant data by region/housing type---
#mapping.calculate_participant_stats_by_region(0, 21)
#mapping.calculate_participant_stats_by_housing_type(0, 21)
#mapping.calculate_counts_of_parvar_by_housing_type(0,25)
#mapping.calculate_counts_of_parvar_by_region(0,19)

mapping = Mapping(["data/dailyroute.csv", "data/recroute.csv", "data/unhappy_places.csv", "data/house.csv"],
                  ["DailyRoute", "RecreationalRoute", "UnhappyPlace", "House"], "data/data.csv")
#---mapobj---
#mapping.count_obj(0)
#mapping.calculate_area(0)
#mapping.calculate_distance(0)
#mapping.calculate_word_counts_from_sent(0, "reason")
#mapping.calculate_grouped_nominal_counts(0, "frequency")
#mapping.calculate_basic_stats(2,"improv_score")
#mapping.calculate_nominal_counts(0, "route_dependency")
#mapping.calculate_facilities_around_map_obj("data/final_tampines_poi.csv",2)

#--mapobj by region--
#mapping.count_mapobj_by_region(3,1)
#mapping.calculate_area_by_region(3, 0)
#mapping.calculate_distance_by_region(3, 1)
#mapping.calculate_word_counts_from_sent_by_region(2,0,"reason")
#mapping.calculate_nominal_counts_by_region(3,1,"route_dependency")
#mapping.calculate_facilities_around_map_obj_by_region("data/final_tampines_poi.csv",3,2)
#mapping.calculate_facilities_around_map_obj_by_pardata("data/final_tampines_poi.csv",46,2)
mapping.calculate_facilities_around_map_obj_by_mapobjattr("data/final_tampines_poi.csv",3,"housing_type",2)

#--mapobj by participant's data--
#mapping.count_mapobj_by_pardata(46, 1)
#mapping.calculate_area_by_pardata(46, 0)
#mapping.calculate_distance_by_pardata(46, 1)
#mapping.calculate_word_counts_from_sent_by_pardata(46,0,"reason")
#mapping.calculate_nominal_counts_by_pardata(46,1,"route_dependency")

#--mapobj by mapobj's attributes--
#mapping.count_mapobj_by_mapobjattr(3, "housing_type", 1)
#mapping.calculate_area_by_mapobjattr(3, "housing_type", 0)
#mapping.calculate_distance_by_mapobjattr(3, "housing_type", 1)
#mapping.calculate_word_counts_from_sent_by_mapobjattr(2, "housing_type", 0,"reason")
#mapping.calculate_nominal_counts_by_mapobjattr(3, "housing_type", 1,"route_dependency")

#--plotting
#mapping.create_heat_map([0],["happy_places"])
#mapping.create_plot_by_age([0],["happy_places_by_age"])
#mapping.create_plot([0],["test"])
#mapping.create_plot_by_region(2, 0)
#mapping.create_plot_by_pardata(46, 0)
#mapping.create_plot_by_mapobjattr(2, "housing_type", 0)

#mapping.plot_route([0],["test"])
#mapping.plot_route_by_region(3, 1)
#mapping.plot_route_by_pardata(46 ,1)
#mapping.plot_route_by_mapobjattr(3, "housing_type", 1)

#--calculate distance or coincidence
#mapping.calculate_place_coincidences(0, 1)
#mapping.calculate_route_coincidences(0,1)
#mapping.calculate_point_route_coincidences(1,2)

#mapping.calculate_place_coincidences_by_region(0,1,2)
#mapping.calculate_route_coincidences_by_region(0,1,3)
#mapping.calculate_point_route_coincidences_by_region(1,2,3)

#mapping.calculate_place_coincidences_by_pardata(0,1,46)
#mapping.calculate_route_coincidences_by_pardata(0,1,46)
#mapping.calculate_point_route_coincidences_by_pardata(1,2,2)

#mapping.calculate_place_coincidences_by_mapobjattr(0,1,2,"housing_type")
#mapping.calculate_route_coincidences_by_mapobjattr(0,1,3,"housing_type")
#mapping.calculate_point_route_coincidences_by_mapobjattr(1,2,3,"housing_type")

'''mapping = Mapping(["data/house.csv"],
                  ["House"], "data/data.csv")'''

#create pandas table
#mapping.merge_mapobj_into_table([46,2,52], [0], ["coordinates"])
#generate_summary_distribution("map_obj_summary.csv")
#generate_impro_suggestion("map_obj_summary.csv")