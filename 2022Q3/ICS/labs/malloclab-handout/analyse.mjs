import fs from "fs";
const traces = fs.readdirSync("traces");
const sizes = new Map();
for (const trace of traces) {
  const data = fs.readFileSync(`traces/${trace}`, "utf8");
  console.log(`Processing ${trace}`);
  const lines = data
    .split("\n")
    .map((l) => l.trim())
    .filter((l) => l);
  const allocations = lines
    .filter((l) => l.startsWith("a"))
    .map((l) => l.split(" "))
    .map(([a, b, c]) => parseInt(c))
    .filter((c) => !Number.isNaN(c))
    .reduce((acc, c) => acc.set(c, (acc.get(c) ?? 0) + 1), new Map());
  allocations.forEach((count, size) => {
    if (size < 2) return;
    sizes.set(size, (sizes.get(size) ?? 0) + count);
  });
}

console.log(
  [...sizes.entries()]
    .sort((a, b) => b[1] - a[1])
    .filter((a) => a[1] > 100)
    .sort((a, b) => a[0] - b[0])
    .forEach((a) => console.log("%d => %d", a[0], a[1]))
);
