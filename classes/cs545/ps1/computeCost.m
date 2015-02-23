function J = computeCost(X, y, theta)
  m = length(y);
  S = X * theta - y;
  J = S' * S / (2 * m);
end
