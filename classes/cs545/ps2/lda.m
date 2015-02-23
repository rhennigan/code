function [w, accuracy ] = lda(X, y)
% Linear Discriminant Analysis

% get the pos and neg data
pos_data = X(find(y), :)
neg_data = X(find(1 - y), :)

% Mean of each class
pos_mean = sum(pos_data) / length(pos_data)
neg_mean = sum(neg_data) / length(neg_data)

% Center the data
pos_data = -pos_mean .+ pos_data
neg_data = %YOUR CODE HERE

% Covariance of the data
cov_all = %YOUR CODE HERE

% Get w and training accuracy
w = %YOUR CODE HERE
accuracy = %YOUR CODE HERE


% Plot Gaussian Ellipsoids
h_pos = plot_gaussian_ellipsoid(pos_mean, cov_all);
h_neg = plot_gaussian_ellipsoid(neg_mean, cov_all);
set(h_pos,'color','r');
set(h_neg,'color','g');
end

