% Linear Discriminant Analysis

function [w, accuracy] = lda(X, y)

  % get the pos and neg data
  X1 = X(find(y), :);
  X2 = X(find(1 - y), :);

  % Mean of each class
  m1 = mean(X1);
  m2 = mean(X2);

  % Center the data
  C1 = bsxfun(@minus, X1, m1);
  C2 = bsxfun(@minus, X2, m2);

  % Covariance of the data
  n1 = length(X1);
  n2 = length(X2);
  S1 = C1' * C1 / n1;
  S2 = C2' * C2 / n2;
  Sw = (S1 + S2) / 2;

  % Get w and training accuracy
  w0 = inv(Sw) * (m1 - m2)';
  w  = w0 / norm(w0);

  % t = (X-mean(X)) * w;
  t = bsxfun(@minus, X, 0.5 * (m1 + m2)) * w;
  t(find(t < 0)) = 0;
  t(find(t > 0)) = 1;
  accuracy = 100 * (1 - sum(abs(t - y)) / length(y));

  % Plot Gaussian Ellipsoids
  h_pos = plot_gaussian_ellipsoid(m1, Sw);
  h_neg = plot_gaussian_ellipsoid(m2, Sw);
  set(h_pos,'color','r');
  set(h_neg,'color','g');

end
