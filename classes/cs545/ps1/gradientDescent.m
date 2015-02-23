function [theta, J_history] = gradientDescent(X, y, theta, alpha, num_iters)
  m = length(y);
  J_history = zeros(num_iters, 1);
  for iter = 1:num_iters
    theta = theta - (alpha * (((theta' * X')' - y)' * X) / m)';
    J_history(iter) = computeCost(X, y, theta);
  end
end
