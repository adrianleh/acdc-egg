import json
import sys
import requests

def read_lemmas_json(filename):
  with open(filename, 'r') as f:
    data = json.load(f)
  return data
  
def get_sublemmas(data, start, to):  
  try:
    lemmas = data["params"][0][start:to]
  except (KeyError, IndexError, TypeError):
    raise ValueError("Invalid JSON structure for lemmas")
  new_data = data.copy()
  new_data["params"][0] = lemmas
  return new_data

def send_json_to_endpoint(data, endpoint="http://localhost:8080/api"):
  print(f"Sending data to endpoint: {json.dumps(data)}", file=sys.stderr)
  try:
    response = requests.post(endpoint, json=data)
    response.raise_for_status()
    return response.json()
  except requests.RequestException as e:
    print(f"Error sending JSON to endpoint: {e}")
    return None
  
def find_minimal_lemmas(data, endpoint="http://localhost:8080/api"):
  lemmas_list = data["params"][0]
  last_err = data
  left, right = 0, len(lemmas_list)
  while left < right:
    mid = (left + right) // 2
    sub_data = get_sublemmas(data, left, right)
    result = send_json_to_endpoint(sub_data, endpoint)
    # print(result, file=sys.stderr)
    if result and "error" in result:
      print("SETTNG last_err", file=sys.stderr)
      last_err = sub_data
      right = mid
    else:
      print("NOT SETTING last_err", file=sys.stderr)
      left = mid + 1
    print("-----------------", file=sys.stderr)
  print(f"Final minimal error-inducing subset: {last_err}", file=sys.stderr)
  return last_err


if __name__ == "__main__":
  if len(sys.argv) != 2:
    print(f"Usage: {sys.argv[0]} <lemmas.json>")
    sys.exit(1)
  filename = sys.argv[1]
  lemmas = read_lemmas_json(filename)
  minimal_lemmas = find_minimal_lemmas(lemmas)
  print("Minimal lemmas causing the error:", file=sys.stderr)
  print(json.dumps(minimal_lemmas))