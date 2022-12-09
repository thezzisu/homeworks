let arr = [2, 1, 3, 5, 0, 6, 4, 5, 0, 4, 1, 2, 1, 1];
let check = (a1, a2) => {
  let v2 = a1;
  for (let i = 0; i < a2.length; i++)
    v2 = arr[v2 + 7 * (a2[i].charCodeAt(0) - 48)];
  return v2;
};
let fuck = (a1) => {
  let v1 = check(0, a1);
  for (let i = 1; i <= 6; i++) {
    if (check(i, a1) !== v1) return false;
  }
  return true;
};
for (let len = 1; len <= 13; len++) {
  for (let i = 0; i < parseInt("1111111111111", 2); i++) {
    if (fuck(i.toString(2).padStart(len, "0")))
      console.log(i.toString(2).padStart(len, "0"));
  }
}
