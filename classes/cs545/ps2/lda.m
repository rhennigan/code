function [w, accuracy ] = lda(X, y)
% Linear Discriminant Analysis

% get the pos and neg data
% pos_data = X(find(y), :)
% neg_data = X(find(1 - y), :)

% % Mean of each class
% pos_mean = mean(pos_data)
% neg_mean = mean(neg_data)

% % Center the data
% pos_data = bsxfun(@minus, pos_data, mean([pos_mean; neg_mean]))
% neg_data = bsxfun(@minus, neg_data, mean([pos_mean; neg_mean]))

% % Covariance of the data
% cov_all = (pos_data' * pos_data + neg_data' * neg_data) / length(X)

X1 = X(find(y), :);
X2 = X(find(1 - y), :);

m1 = mean(X1);
m2 = mean(X2);

S1 = (X1-m1)' * (X1-m1) / length(X1);
S2 = (X2-m2)' * (X2-m2) / length(X2);
Sw = S1 + S2;
w0 = inv(Sw) * (m1 - m2)';
w  = w0 / norm(w0);
t = (X-mean(X)) * w;

for i = 1:length(X)
  

% Get w and training accuracy
% w = %YOUR CODE HERE
% accuracy = %YOUR CODE HERE

pos_mean = m1;
neg_mean = m2;

% Plot Gaussian Ellipsoids

h_pos = plot_gaussian_ellipsoid(pos_mean, Sw / 2);
h_neg = plot_gaussian_ellipsoid(neg_mean, Sw / 2);
set(h_pos,'color','r');
set(h_neg,'color','g');
end

