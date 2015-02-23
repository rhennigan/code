function [w, accuracy] = lda(X, y)
% Linear Discriminant Analysis


% pos_data = X(find(y), :)
% neg_data = X(find(1 - y), :)

% 
% pos_mean = mean(pos_data)
% neg_mean = mean(neg_data)

% 
% pos_data = bsxfun(@minus, pos_data, mean([pos_mean; neg_mean]))
% neg_data = bsxfun(@minus, neg_data, mean([pos_mean; neg_mean]))

% % Covariance of the data
% cov_all = (pos_data' * pos_data + neg_data' * neg_data) / length(X)

% get the pos and neg data
X1 = X(find(y), :);
X2 = X(find(1 - y), :);

% Mean of each class
m1 = mean(X1);
m2 = mean(X2);

% Center the data
C1 = bsxfun(@minus, X1, m1);
C2 = bsxfun(@minus, X2, m2);

n1 = length(X1);
n2 = length(X2);

S1 = C1' * C1 / n1;
S2 = C2' * C2 / n2;
Sw = (S1 + S2) / 2;
w0 = inv(Sw) * (m1 - m2)';
w  = w0 / norm(w0);
% t = (X-mean(X)) * w;
t = bsxfun(@minus, X, 0.5 * (m1 + m2)) * w;
t(find(t<0)) = 0;
t(find(t>0)) = 1;

accuracy = 100 * (1 - sum(abs(t-y)) / length(y));

% Get w and training accuracy
% w = %YOUR CODE HERE
% accuracy = %YOUR CODE HERE

pos_mean = m1;
neg_mean = m2;

% Plot Gaussian Ellipsoids

h_pos = plot_gaussian_ellipsoid(pos_mean, Sw);
h_neg = plot_gaussian_ellipsoid(neg_mean, Sw);
set(h_pos,'color','r');
set(h_neg,'color','g');
end
