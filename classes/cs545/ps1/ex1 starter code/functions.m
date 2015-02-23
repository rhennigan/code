function A = warmUpExercise()
  A = ones(5);
end

function plotData(x, y)
  figure;
  plot(x, y, 'rx', 'MarkerSize', 10);
  ylabel('Profit in $10,000s');
  xlabel('Population of City in 10,000s');
end

function J = computeCost(X, y, theta)
  m = length(y);
  S = X * theta - y;
  J = S' * S / (2 * m);
end

function [theta, J_history] = gradientDescent(X, y, theta, alpha, num_iters)
  m = length(y);
  J_history = zeros(num_iters, 1);
  for iter = 1:num_iters
    theta = theta - (alpha * (((theta' * X')' - y)' * X) / m)';
    J_history(iter) = computeCost(X, y, theta);
  end
end
