#include <iostream>

#include "json/JsonHelper.h"

using namespace llvm;

/* ========== Tracked Vals Data ========== */

/*
 * Every time we analyse a function, we:
 * 1. Read from JSON file
 * 2. Add entry to JSON-derived map
 * 3. Write new map to JSON file
 */
void
JsonHelper::doTrackedValsJson(std::string filename,
                              TrackedValuesResult &FuncBBTrackedVals,
                              TrackedValuesMap_JSON &FuncBBTrackedVals_JSON,
                              Function *F) {
  Json::Value root; // root will contain the root value

  struct stat buffer;
  if (stat (filename.c_str(), &buffer) == 0) {
    // file exists; open json file
    std::cout << "JSON File Exists\n";
    std::ifstream json_file(filename, std::ifstream::binary);
    json_file >> root;
    loadTrackedValuesJsonObjToJsonMap(root, FuncBBTrackedVals_JSON);
  } else {
    // file does not exist; make new json file
    std::cout << "JSON File does not exist\n";
    Json::Value emptyRoot = Json::objectValue;
    writeJsonObjToFile(emptyRoot, filename);
  }

  // Update JsonMap with tracked values information from this func:
  updateJsonMapWithFuncTrackedValues(FuncBBTrackedVals_JSON, FuncBBTrackedVals, F);
  // printJsonMap(FuncBBTrackedVals_JSON);

  // Write (overwrite) updated FunBBTrackedVals_JSON back to json file:
  writeJsonMapToJsonObj(FuncBBTrackedVals_JSON, root);
  writeJsonObjToFile(root, filename);
}

void
JsonHelper::loadTrackedValuesJsonObjToJsonMap(
  Json::Value root,
  TrackedValuesMap_JSON &jsonMap)
{
  // read json data into map.
  Json::Value::const_iterator root_itr;
  Json::Value::const_iterator func_iter;
  Json::Value::const_iterator bb_iter;
  // iterate over funcs in json:
  for (root_itr = root.begin(); root_itr != root.end() ; root_itr++) 
  {
    std::string funcName = root_itr.key().asString();
    Json::Value funcBBs = root[funcName];
    // iterate over BBs in func:
    BBTrackedVals_JSON bbTrackedVals;
    for (func_iter = funcBBs.begin(); func_iter != funcBBs.end(); func_iter++) 
    {
      std::string bbName = func_iter.key().asString();
      Json::Value bbVals = funcBBs[bbName]["tracked values"];
      // iterate over tracked vals in BB:
      std::set<std::string> trackedVals;
      for (bb_iter = bbVals.begin(); bb_iter != bbVals.end(); bb_iter++) 
      {
        std::string valName = (*bb_iter).asString();
        trackedVals.emplace(valName);
      }
      bbTrackedVals.emplace(bbName, trackedVals);
    }
    jsonMap.emplace(funcName, bbTrackedVals);
  }
}

void
JsonHelper::updateJsonMapWithFuncTrackedValues(
  TrackedValuesMap_JSON &jsonMap,
  TrackedValuesResult &trackedValsMap,
  Function *F)
{
  const Module *M = F->getParent();
  LiveValues::BBTrackedVals::const_iterator bbIt;
  std::set<const Value *>::const_iterator valIt;
  if (trackedValsMap.count(F))
  {
    BBTrackedVals_JSON jsonBBTrackedVals;
    const std::string funcName = getOpName(F, M);
    for(bbIt = trackedValsMap.at(F).cbegin();
        bbIt != trackedValsMap.at(F).cend();
        bbIt++)
    {
      std::set<std::string> jsonTrackedVals;
      std::string bbName = getOpName(bbIt->first, M);
      const std::set<const Value *> &trackedVals = bbIt->second;
      for(valIt = trackedVals.cbegin(); valIt != trackedVals.cend(); valIt++)
      {        
        // Capture printAsOperand output, since value names don't actually 
        // exist and are allocated only during printing.
        std::string valName = getOpName(*valIt, M);
        jsonTrackedVals.emplace(valName);
      }
      jsonBBTrackedVals.emplace(bbName, jsonTrackedVals);
    }
    // update / add to json map:
    jsonMap[funcName] = jsonBBTrackedVals;
  }
}

void
JsonHelper::writeJsonMapToJsonObj(
  TrackedValuesMap_JSON &jsonMap, 
  Json::Value &root)
{
  TrackedValuesMap_JSON::const_iterator f_it;
  for (f_it = jsonMap.cbegin(); f_it != jsonMap.cend(); f_it++)
  {
    std::string funcName = f_it->first;
    BBTrackedVals_JSON bbTrackedVals = f_it->second;
    BBTrackedVals_JSON::const_iterator bb_it;
    if (bbTrackedVals.empty()) {
      root[funcName] = Json::objectValue;
      continue;
    }
    for (bb_it = bbTrackedVals.cbegin(); bb_it != bbTrackedVals.cend(); bb_it++)
    {
      std::string bbName = bb_it->first;
      std::set<std::string> trackedValsNames = bb_it->second;
      if (trackedValsNames.empty()) {
        root[funcName][bbName] = Json::objectValue;
        continue;
      }
      Json::Value trackedValsList;
      for (std::string valName : trackedValsNames)
      {
        trackedValsList.append(valName);
      }
      root[funcName][bbName]["tracked values"] = trackedValsList;
    }
  }
}

void
JsonHelper::printJsonMap(TrackedValuesMap_JSON &json_map)
{
  TrackedValuesMap_JSON::const_iterator f_it;
  for (f_it = json_map.cbegin(); f_it != json_map.cend(); f_it++)
  {
    std::string funcName = f_it->first;
    BBTrackedVals_JSON bbTrackedVals = f_it->second;
    std::cout << funcName << ": \n";

    BBTrackedVals_JSON::const_iterator bb_it;
    for (bb_it = bbTrackedVals.cbegin(); bb_it != bbTrackedVals.cend(); bb_it++)
    {
      std::string bbName = bb_it->first;
      std::set<std::string> trackedVals = bb_it->second;
      std::cout << "  " << bbName << ": \n    ";

      for (std::string val : trackedVals)
      {
        std::cout << val << " ";
      }
      std::cout << "\n";
    }
  }
}

JsonHelper::TrackedValuesMap_JSON
JsonHelper::getTrackedValuesResultsFromJson(const std::string filename)
{
  Json::Value root; // root will contain the root value
  LiveValues::TrackedValuesMap_JSON jsonMap;
  struct stat buffer;
  if (stat (filename.c_str(), &buffer) == 0)
  {
    // file exists; open json file
    std::cout << "JSON File Exists\n";
    std::ifstream json_file(filename, std::ifstream::binary);
    json_file >> root;
    loadTrackedValuesJsonObjToJsonMap(root, jsonMap);
  }
  else
  {
    // file does not exist; make new json file
    std::cout << "JSON File does not exist\n";
    throw std::runtime_error("Required JSON file " + filename + " does not exist!");
  }
  return jsonMap;
}

LiveValues::TrackedValuesResult
JsonHelper::getFuncBBTrackedValsMap(
  const SubroutineInjection::FuncValuePtrsMap &funcValuePtrsMap,
  const LiveValues::TrackedValuesMap_JSON &jsonMap,
  Module &M
)
{
  LiveValues::TrackedValuesResult funcBBTrackedValsMap;
  for (auto &F : M.getFunctionList())
  {
    std::string funcName = JsonHelper::getOpName(&F, &M);
    // std::cout<<"\n"<<funcName<<":\n";
    if (jsonMap.count(funcName) && funcValuePtrsMap.count(&F))
    {
      SubroutineInjection::ValuePtrsMap valuePtrsMap = funcValuePtrsMap.at(&F);
      LiveValues::BBTrackedVals_JSON bbTrackedVals_json = jsonMap.at(funcName);
      LiveValues::BBTrackedVals bbTrackedValsMap;
      Function::iterator bbIter;
      for (bbIter = F.begin(); bbIter != F.end(); ++bbIter)
      {
        const BasicBlock* bb = &(*bbIter);
        std::string bbName = JsonHelper::getOpName(bb, &M);
        // std::cout<<"  "<<bbName<<":\n    ";
        std::set<const Value*> trackedVals;
        if (bbTrackedVals_json.count(bbName))
        {
          // get names of tracked values in this BB from json map
          std::set<std::string> trackedVals_json = bbTrackedVals_json.at(bbName);
          std::set<std::string>::const_iterator valIt;
          for (valIt = trackedVals_json.cbegin(); valIt != trackedVals_json.cend(); valIt++)
          {
            std::string valName = *valIt;
            if (valuePtrsMap.count(valName))
            {
              // get pointers to values corresponding to value name
              const Value* val = valuePtrsMap.at(valName);
              trackedVals.insert(val);
              // std::cout<<JsonHelper::getOpName(val, &M)<< " ";
            }
          }
          // std::cout<<"\n";
        }
        bbTrackedValsMap.emplace(bb, trackedVals);
      }
      // std::cout<<"\n";
      funcBBTrackedValsMap.emplace(&F, bbTrackedValsMap);
    }
    else
    {
      std::cout << "No tracked values analysis data for '" << funcName << "'\n";
    }
  }
  return funcBBTrackedValsMap;
}

/* ========== Live-in Live-out Vals Data ========== */

void
JsonHelper::doLiveValsJson(std::string filename,
			   LivenessResult &FuncLiveVals,
			   LiveValues::VariableDefMap &mapVars,
			   LiveValuesMap_JSON &FuncBBLiveVals_JSON,
			   Function *F)
{
  Json::Value root; // root will contain the root value

  struct stat buffer;
  if (stat (filename.c_str(), &buffer) == 0) {
    // file exists; open json file
    std::cout << "JSON File Exists\n";
    std::ifstream json_file(filename, std::ifstream::binary);
    json_file >> root;
    loadLiveValuesJsonObjToJsonMap(root, FuncBBLiveVals_JSON);
  } else {
    // file does not exist; make new json file
    std::cout << "JSON File does not exist\n";
    Json::Value emptyRoot = Json::objectValue;
    writeJsonObjToFile(emptyRoot, filename);
  }

  // Update JsonMap with tracked values information from this func:
  updateJsonMapWithFuncLiveValues(FuncBBLiveVals_JSON, FuncLiveVals, mapVars, F);
  // printJsonMap(FuncBBLiveVals_JSON);

  // Write (overwrite) updated FunBBTrackedVals_JSON back to json file:
  writeJsonMapToJsonObj(FuncBBLiveVals_JSON, root);
  writeJsonObjToFile(root, filename);
}

void
JsonHelper::loadLiveValuesJsonObjToJsonMap(Json::Value root, LiveValuesMap_JSON &jsonMap)
{
  // read json data into map.
  Json::Value::const_iterator root_itr;
  Json::Value::const_iterator func_iter;
  Json::Value::const_iterator bb_iter;
  // iterate over funcs in json:
  for (root_itr = root.begin(); root_itr != root.end() ; root_itr++) 
  {
    std::string funcName = root_itr.key().asString();
    Json::Value funcBBs = root[funcName];
    // iterate over BBs in func:
    BBLiveVals_JSON bbLiveVals;
    for (func_iter = funcBBs.begin(); func_iter != funcBBs.end(); func_iter++) 
    {
      std::string bbName = func_iter.key().asString();
      // process live-in vals for BB:
      Json::Value bbLiveInVals = funcBBs[bbName]["live-in"];
      std::set<std::pair<std::string, int>> liveInVals;
      //std::set<std::string> liveInVals;
      int inter_idx = 0;
      std::string valName;
      for (bb_iter = bbLiveInVals.begin(); bb_iter != bbLiveInVals.end(); bb_iter++) 
      {
        // odd inter_idx corresponds to Value name, even corresponds to Value size in bytes
        inter_idx++;
        if((inter_idx%2) == 1)
          valName = (*bb_iter).asString();
        else{
          int size = (*bb_iter).asInt();
          liveInVals.emplace(std::pair<std::string, int>(valName, size));
        }
      }
      // process live-out vals for BB:
      Json::Value bbLiveOutVals = funcBBs[bbName]["live-out"];
      std::set<std::pair<std::string, int>> liveOutVals;
      //std::set<std::string> liveOutVals;
      inter_idx = 0;
      for (bb_iter = bbLiveOutVals.begin(); bb_iter != bbLiveOutVals.end(); bb_iter++)
      {
        inter_idx++;
        if((inter_idx%2) == 1)
          valName = (*bb_iter).asString();
        else{
          int size = (*bb_iter).asInt();
          liveOutVals.emplace(std::pair<std::string, int>(valName, size));
        }
      }
      
      LiveInOutData_JSON jsonLiveInOut = {
        .liveInVals_json = liveInVals,
        .liveOutVals_json = liveOutVals
      };
      bbLiveVals.emplace(bbName, jsonLiveInOut);
    }
    jsonMap.emplace(funcName, bbLiveVals);
  }
}

/* Updates the in-memory map jsonMap with live Values for this function.*/
void
JsonHelper::updateJsonMapWithFuncLiveValues(LiveValuesMap_JSON &jsonMap,
                                            LivenessResult &liveValsMap,
					                                  LiveValues::VariableDefMap &mapVars,
                                            Function *F)
{
  int varValue = 1;
  std::map<const Value *, int>::iterator it;
  const Module *M = F->getParent();
  LiveValues::BBLiveVals::const_iterator bbIt;
  std::set<const Value *>::const_iterator valIt;
  if (liveValsMap.count(F))
  {
    BBLiveVals_JSON jsonBBLiveVals;
    const std::string funcName = getOpName(F, M);
    for(bbIt = liveValsMap.at(F).cbegin();
        bbIt != liveValsMap.at(F).cend();
        bbIt++)
    {
      std::string bbName = getOpName(bbIt->first, M);

      // process live-in values:
      //std::set<std::string> jsonLiveInVals;
      std::set<std::pair<std::string, int>> jsonLiveInVals;
      const std::set<const Value *> &liveInVals = bbIt->second.liveInVals;
      for(valIt = liveInVals.cbegin(); valIt != liveInVals.cend(); valIt++)
      {        
        std::string valName = getOpName(*valIt, M);
        varValue = 1;
        it = mapVars.find(*valIt); 
        if (it != mapVars.end())
          varValue = it->second;
        jsonLiveInVals.emplace(std::pair<std::string, int>(valName, varValue));
        //jsonLiveInVals.emplace(valName);
      }
      // process live-out values:
      //std::set<std::string> jsonLiveOutVals;
      std::set<std::pair<std::string, int>> jsonLiveOutVals;
      const std::set<const Value *> &liveOutVals = bbIt->second.liveOutVals;
      for(valIt = liveOutVals.cbegin(); valIt != liveOutVals.cend(); valIt++)
      {        
        std::string valName = getOpName(*valIt, M);
        varValue = 1;
        it = mapVars.find(*valIt); 
        if (it != mapVars.end())
          varValue = it->second;
        jsonLiveOutVals.emplace(std::pair<std::string, int>(valName, varValue));
        //jsonLiveOutVals.emplace(valName);
      }

      LiveInOutData_JSON jsonLiveInOutData = {
        .liveInVals_json = jsonLiveInVals,
        .liveOutVals_json = jsonLiveOutVals
      };
      jsonBBLiveVals.emplace(bbName, jsonLiveInOutData);
    }
    // update / add to json map:
    jsonMap[funcName] = jsonBBLiveVals;
  }
}

void
JsonHelper::writeJsonMapToJsonObj(
  LiveValuesMap_JSON &jsonMap, 
  Json::Value &root)
{
  LiveValuesMap_JSON::const_iterator f_it;
  for (f_it = jsonMap.cbegin(); f_it != jsonMap.cend(); f_it++)
  {
    std::string funcName = f_it->first;
    BBLiveVals_JSON bbLiveVals = f_it->second;
    BBLiveVals_JSON::const_iterator bb_it;
    if (bbLiveVals.empty()) {
      root[funcName] = Json::objectValue;
      continue;
    }
    for (bb_it = bbLiveVals.cbegin(); bb_it != bbLiveVals.cend(); bb_it++)
    {
      std::string bbName = bb_it->first;
      //const std::set<std::string> liveInValsNames = bb_it->second.liveInVals_json;
      //const std::set<std::string> liveOutValsNames = bb_it->second.liveOutVals_json;
      const std::set<std::pair<std::string, int>> liveInValsNames = bb_it->second.liveInVals_json;
      const std::set<std::pair<std::string, int>> liveOutValsNames = bb_it->second.liveOutVals_json;

      if (liveInValsNames.empty() && liveOutValsNames.empty()) {
        root[funcName][bbName] = Json::objectValue;
        continue;
      }

      // create & add list of live-in value names
      Json::Value liveInValsList;
      for (std::pair<std::string, int> valName : liveInValsNames)
      {
        liveInValsList.append(valName.first);
	      liveInValsList.append(valName.second);
      }
      root[funcName][bbName]["live-in"] = liveInValsList;

      // create & add list of live-out value names
      Json::Value liveOutValsList = Json::Value{};
      for(std::pair<std::string, int> valName : liveOutValsNames)
      {
        liveOutValsList.append(Json::Value(static_cast<const std::string>(valName.first)));
        liveOutValsList.append(valName.second);
      }
      root[funcName][bbName]["live-out"] = liveOutValsList;
    }
  }
}

void
JsonHelper::printJsonMap(LiveValuesMap_JSON &json_map)
{
  LiveValuesMap_JSON::const_iterator f_it;
  for (f_it = json_map.cbegin(); f_it != json_map.cend(); f_it++)
  {
    std::string funcName = f_it->first;
    BBLiveVals_JSON bbLiveVals = f_it->second;
    std::cout << funcName << ": \n";

    BBLiveVals_JSON::const_iterator bb_it;
    for (bb_it = bbLiveVals.cbegin(); bb_it != bbLiveVals.cend(); bb_it++)
    {
      std::string bbName = bb_it->first;
      //std::set<std::string> liveInVals = bb_it->second.liveInVals_json;
      //std::set<std::string> liveOutVals = bb_it->second.liveOutVals_json;

      std::set<std::pair<std::string, int>> liveInVals = bb_it->second.liveInVals_json;
      std::set<std::pair<std::string, int>> liveOutVals = bb_it->second.liveOutVals_json;
      
      std::cout << "  " << bbName << ": \n";

      std::cout << "    live-in:\n        ";
      for (std::pair<std::string, int> val : liveInVals)
      {
        std::cout << val.first << " (" << val.second << ") " ;
      }
      std::cout << "\n";

      std::cout << "    live-out:\n        ";
      for (std::pair<std::string, int> val : liveOutVals)
      {
	      std::cout << val.first << " (" << val.second << ") " ;
      }
      std::cout << "\n";
    }
  }
}

JsonHelper::LiveValuesMap_JSON
JsonHelper::getLiveValuesResultsFromJson(const std::string filename)
{
  Json::Value root;
  LiveValues::LiveValuesMap_JSON jsonMap;
  struct stat buffer;
  if (stat (filename.c_str(), &buffer) == 0)
  {
    // file exists; open json file
    std::cout << "JSON File Exists\n";
    std::ifstream json_file(filename, std::ifstream::binary);
    json_file >> root;
    loadLiveValuesJsonObjToJsonMap(root, jsonMap);
  }
  else
  {
    // file does not exist; make new json file
    std::cout << "JSON File does not exist\n";
    throw std::runtime_error("Required JSON file " + filename + " does not exist!");
  }
  return jsonMap;
}

std::pair<LiveValues::LivenessResult, LiveValues::FuncVariableDefMap>
JsonHelper::getFuncBBLiveValsInfo(
  const SubroutineInjection::FuncValuePtrsMap &funcValuePtrsMap,
  const LiveValues::LiveValuesMap_JSON &jsonMap,
  Module &M
)
{
  LiveValues::FuncVariableDefMap funcValDefMap;
  LiveValues::LivenessResult funcBBLiveValsMap;
  for (auto &F : M.getFunctionList())
  {
    LiveValues::VariableDefMap valSizeMap;
    std::string funcName = JsonHelper::getOpName(&F, &M);
    // std::cout<<"\n"<<funcName<<":\n";
    if (jsonMap.count(funcName) && funcValuePtrsMap.count(&F))
    {
      // std::cout<<JsonHelper::getOpName(&F, &M)<<"\n";
      SubroutineInjection::ValuePtrsMap valuePtrsMap = funcValuePtrsMap.at(&F);
      LiveValues::BBLiveVals_JSON bbLiveVals_json = jsonMap.at(funcName);
      LiveValues::BBLiveVals bbLiveValsMap;
      Function::iterator bbIter;
      for (bbIter = F.begin(); bbIter != F.end(); ++bbIter)
      {
        const BasicBlock* bb = &(*bbIter);
        std::string bbName = JsonHelper::getOpName(bb, &M);
        // std::cout<<"  "<<bbName<<":\n";
        std::set<const Value*> liveInVals;
        std::set<const Value*> liveOutVals;
        if (bbLiveVals_json.count(bbName))
        {
          // get names of live-in/out values in this BB from json map
          //std::set<std::string> liveInVals_json = bbLiveVals_json.at(bbName).liveInVals_json;
          //std::set<std::string> liveOutVals_json = bbLiveVals_json.at(bbName).liveOutVals_json;
	        std::set<std::pair<std::string, int>> liveInVals_json = bbLiveVals_json.at(bbName).liveInVals_json;
          std::set<std::pair<std::string, int>> liveOutVals_json = bbLiveVals_json.at(bbName).liveOutVals_json;

          // process live-in values
          // std::cout<<"    live-in\n        ";
          std::set<std::pair<std::string, int>>::const_iterator valIt;
          for (valIt = liveInVals_json.cbegin(); valIt != liveInVals_json.cend(); valIt++)
          {
            std::string valName = (*valIt).first;
            int valSize = (*valIt).second;
            if (valuePtrsMap.count(valName))
            {
              // get pointers to values corresponding to value name
              const Value* val = valuePtrsMap.at(valName);
              liveInVals.insert(val);
              valSizeMap.emplace(val, valSize);
              // std::cout<<JsonHelper::getOpName(val, &M)<< " ";
            }
          }
          // std::cout<<"\n";

          // process live-out values
          // std::cout<<"    live-out\n        ";
          for (valIt = liveOutVals_json.cbegin(); valIt != liveOutVals_json.cend(); valIt++)
          {
            std::string valName = (*valIt).first;
            int valSize = (*valIt).second;
            if (valuePtrsMap.count(valName))
            {
              // get pointers to values corresponding to value name
              const Value* val = valuePtrsMap.at(valName);
              liveOutVals.insert(val);
              valSizeMap.emplace(val, valSize);
              // std::cout<<JsonHelper::getOpName(val, &M)<< " ";
            }
          }
          // std::cout<<"\n";
        }
        LiveValues::LiveInOutData liveInOutData = {
          .liveInVals = liveInVals,
          .liveOutVals = liveOutVals
        };
        bbLiveValsMap.emplace(bb, liveInOutData);
      }
      // std::cout<<"\n";
      funcBBLiveValsMap.emplace(&F, bbLiveValsMap);
      funcValDefMap.emplace(&F, valSizeMap);
    }
    else
    {
      std::cout << "No tracked values analysis data for '" << funcName << "'\n";
    }
  }
  std::pair<LiveValues::LivenessResult, LiveValues::FuncVariableDefMap> returnPair(funcBBLiveValsMap, funcValDefMap);
  return returnPair;
}

/* ========== Ckpt Size Data ========== */
void
JsonHelper::writeFuncCkptSizesToJson(FuncCkptSizeMap funcCkptSizeMap, std::string filename)
{
  Json::Value root = Json::objectValue;
  for (auto fIter : funcCkptSizeMap)
  {
    Module *M = fIter.first->getParent();
    std::string funcName = getOpName(fIter.first, M);
    root[funcName] = Json::objectValue;
    for (auto bbIter : fIter.second)
    {
      std::string bbName = getOpName(bbIter.first, M);
      root[funcName][bbName] = bbIter.second;
    }
  }
  writeJsonObjToFile(root, filename);
}

/* ========== Utilility Methods ========== */

void
JsonHelper::writeJsonObjToFile(Json::Value &root, std::string filename)
{
  Json::StyledWriter styledWriter;
  std::ofstream outfile(filename);
  outfile << styledWriter.write(root);
  outfile.close();
}

std::string
JsonHelper::getOpName(const Value *value_ptr, const Module *M)
{
  std::string valNameStr;
  raw_string_ostream rso(valNameStr);
  value_ptr->printAsOperand(rso, false, M);
  return rso.str();
}

std::string
JsonHelper::getOpName(const BasicBlock *bb_ptr, const Module *M)
{
  return JsonHelper::getOpName(dyn_cast<Value>(bb_ptr), M);
}

std::string
JsonHelper::getOpName(const Function *func_ptr, const Module *M)
{
  return JsonHelper::getOpName(dyn_cast<Value>(func_ptr), M);
}
