import math

N = 700
g3 = [0, 0, 0] # Start by initializing g3(0)=g3(1)=g3(2)=0
eta = [0, 0, 0]
eta_initial = 0.125 # Usually, the quantity eta will be fixed at 1/8

####### Section 1: Function definitions ########
####### These functions verify that the necessary assumptions hold and compute bounds on the relevant variables. #######

def bip(x): # Maximum number of edges in a bipartite graph on x vertices
	return math.ceil(x/2)*math.floor(x/2)

def F(A, B, C): # Compute F(A, B, C) according to the proof of Lemma 4.9
	if A <= 0 or B <= 0:
		return 0
	# WLOG assume that A >= B
	if A < B:
		A, B = B, A
	l = math.ceil((A + B) / C)
	last_piece = A + B - (l - 1) * C  # Compute a_l + b_l
	if (A - B) / l > (A + B) - (l - 1) * C:
		D_prime = (A + B) - (l - 1) * C
		D = ((A - B) - D_prime) / (l - 1)  # Using (l - 1) * D + D' = A - B
	else:
		D = D_prime = (A - B) / l
	# ai * bi = ((ai + bi)^2 - (ai - bi)^2) / 4
	return A * B - (l - 1) * (C * C - D * D) / 4 - (last_piece ** 2 - D_prime ** 2) / 4

def w_is_large_enough(s, t, w, k, n): # Used to check condition on w in assumption of Lemma 4.15
	s_diff = max(s - k/t - w, 0)
	t_diff = max(t - k/s - w, 0)
	return s*(t_diff**2) + t*(s_diff**2) + (s-t)**2 <= n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - 4*k


def check_assumptions(n, Delta, P): # Check that the assumptions of Lemmas 4.7, 4.13, and 4.15 hold
	if math.ceil(12*g3[n] / (n*(n-1))) < math.ceil(n/2):
		return False # Assumption of Lemma 4.7 is violated
	if n*(n+1)*(n-1)/3-8*(g3[n]+1) >= n**2 / 4: 
		return False # First assumption of Lemma 4.15 violated
	for s in range(1, n-1):
		for t in range(max(1, math.ceil(n/2)-s), n-s): # Generate pairs (s,t) with ceil(n/2) <= s+t <= n-1
			# We can eliminate pairs which are not admissible according to Definition 4.6
			if abs(s-t) > Delta:
				continue # Violates Definition 4.6(b)
			if s*t + bip(n-1-s-t) < g3[n]-g3[n-1]+1: # Violates Definition 4.6(d)
				continue
			if s*t < 8*math.floor(P/2): # eta <= 1/8 doesn't hold
				# Ensure pair satisfies Definiton 4.6(c)
				min_d1_plus_d2 = n-1 # We now compute S = min_d1_plus_d2 satisfying Definition 4.6(c)
				for d1 in range(1, s+t+1):
					for d2 in range(1, d1+1):
						if bip(d1) + math.floor((n-1-d1)/d2) * bip(d2) + bip((n-1-d1)%d2) > g3[n]-g3[n-1]:
							min_d1_plus_d2 = min(min_d1_plus_d2, d1+d2)
							break # Looking for smallest possible satisfying the inequality, so no point looking any further
				if min_d1_plus_d2 > 8/9*n:
					continue # (s,t) violates Definition 4.6(c)
				eta[n] = max(eta[n], math.floor(P/2)/(s*t)) # Otherwise we update eta
			if F(s, t - math.floor(P/(2*s)), math.floor((s+t+Delta)/2)) <= P:
				return False # Assumption of Lemma 4.13 is violated
			for k in range(math.floor(P/2) + 1): # We now check the second assumption of Lemma 4.15
				# We first compute w
				if not w_is_large_enough(s, t, n-s-t, k, n):
					continue # If even w=n-s-t does not work, then no w works
				w_left = 1
				w_right = n - s - t + 1 # Binary search for w
				while w_right - w_left > 1:
					w_middle = math.floor((w_left+w_right)/2)
					if w_is_large_enough(s, t, w_middle-1, k, n):
						w_right = w_middle
					else:
						w_left = w_middle
				w = w_left
				if F(s, w - (math.floor(P/2) - k - w*k/t)/s, math.floor((s+t+Delta)/2)) <= P - 2*k + w*k/t:
					return False # (6) of Lemma 4.15 is violated
				if F(w, s - (math.floor(P/2) - k - w*k/t)/w, math.floor((s+t+Delta)/2)) <= P - 2*k + w*k/t:
					return False # (7) of Lemma 4.15 is violated
	return True # If we get here, all assumptions hold

# For n >= 70, helper function to find b_max according to Lemma B.2
def b_is_valid(x_star, y_star, u, b, tau):
	n = x_star + y_star + u
	return (u-b)*y_star + bip(x_star-1) + bip(b) + tau - b >= g3[n]-g3[n-1]+1

# For n < 70, helper function to find b_max according to Lemma B.3
def b_is_valid_small_n(x_star, y_star, u, b, tau, Delta):
	n = x_star + y_star + u
	b_prime = max(0, y_star - (u-b+Delta)) # This is the lower possible value for b'
	if (u - b) * (y_star - b_prime) + bip(x_star-1) + bip(b) + bip(b_prime) + tau - b - b_prime >= g3[n]-g3[n-1]+1:
		return True
	b_prime = min(y_star, y_star - (u-b-Delta)) #This is the higher possible value for b'
	if (u - b) * (y_star - b_prime) + bip(x_star-1) + bip(b) + bip(b_prime) + tau - b - b_prime >= g3[n]-g3[n-1]+1:
		return True
	return False 

def max_bad_edges(u, x_star, y_star, Delta, P): # Computes the maximum possible value of tau over all allowed configurations
	n = u + x_star + y_star
	if x_star + y_star < math.ceil(n/2): # Avoid entering the for loop in these cases
		return 0
	max_total_bad_edges = 0 # This is the variable the function returns at the end
	# Main idea: loop over possible values of b_xy and determine whether this combination of x_star, y_star, u, and b_xy is possible according to our lemmas
	# If it is a valid combination, compute tau; if it exceeds max_total_bad_edges, then update max_total_bad_edges
	for b_xy in range(math.floor(P/2)+1): 
		# First compute M_bar, x_bar_max, y_bar_max, x_min, and y_min according to their definitions
		M_bar = min(math.floor((math.floor(P/2) - b_xy) / ((1-eta[n]) * (n/4-Delta/2)) * (1+1/u)), x_star + y_star - math.ceil(n/2))
		if abs(x_star-y_star) > M_bar + Delta:
			return max_total_bad_edges # Lemma 4.17(1) is violated, and since M* is non-increasing in b_xy, the same will be true of larger b_xy
		x_bar_max = M_bar + min(x_star - y_star + Delta, 0)
		y_bar_max = M_bar + min(y_star - x_star + Delta, 0)
		x_min = x_star - x_bar_max
		y_min = y_star - y_bar_max
		# Check that we are in a configuration allowed by Lemma 4.17
		if x_min * max((1-eta[n]) * y_min - u, 0)**2 + y_min * max((1-eta[n]) * x_min - u, 0)**2 > n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - 4*b_xy:
			continue # Lemma 4.17(c) is violated, discard this case
		if x_min * max((1-eta[n]) * u - y_star, 0)**2 + y_min * max((1-eta[n]) * u - x_star, 0)**2 > n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - 4*b_xy:
			continue # Lemma 4.17(d) is violated, discard this case
		# Compute C[b_xy], C[P/2-b_xy], and tau
		C_b_xy = 1 + x_bar_max / x_min + y_bar_max / y_min + u * (x_star + y_star) / (x_min * y_min)
		C_P2_b_xy = (1 + x_bar_max / x_min + y_bar_max / y_min) * (1/x_min + 1/y_min + 1/u)
		tau = math.floor(C_b_xy * b_xy + C_P2_b_xy * (math.floor(P/2) - b_xy) + x_bar_max * y_bar_max)
		# The rest of the function computes an upper bound on max_{X^*} b_U and max_{Y^*} b_U and checking that we are in a configuration allowed by (12) and (13) of Lemma 4.18
		# Two different strategies to bound max_{X^*} b_U and max_{Y^*} b_U, depending on whether n>=70 or n<70
		# For n>=70, if (19) holds, use Lemma B.2 to compute b_max
		if n >= 70 and bip(x_star) + bip(y_star) + bip(u) + tau <= g3[n]-g3[n-1]: 
			# Binary search to find upper bounds on max_{X^*} b_U and max_{Y^*} b_U as outlined by Lemma B.2
			# We call these upper bounds b_max_X and b_max_Y in this code
			# Note that the LHS in (20) is not monotone in b. However, it is convex, so it suffices to do the following:
			# First, test b = u; if it satisfies (20), then b_max = u
			# If b = u doesn't work, test b = 0. If that doesn't work, then by convexity, no b works, and we discard this case
			# If b = u doesn't work while b = 0 does, then we do binary search to find the maximum b satisfying (20)
			if b_is_valid(x_star, y_star, u, u, tau):
				b_max_X = u
			else:
				if not b_is_valid(x_star, y_star, u, 0, tau):
					continue # Discard this case
				b_max_X_left = 0
				b_max_X_right = u + 1
				while b_max_X_right - b_max_X_left > 1:
					b_max_X_middle = math.floor((b_max_X_left + b_max_X_right) / 2)
					if b_is_valid(x_star, y_star, u, b_max_X_middle, tau):
						b_max_X_left = b_max_X_middle
					else:
						b_max_X_right = b_max_X_middle
				b_max_X = b_max_X_left
			# Same idea to find b_max_Y
			if b_is_valid(y_star, x_star, u, u, tau):
				b_max_Y = u
			else:
				if not b_is_valid(y_star, x_star, u, 0, tau):
					continue # Discard this case
				b_max_Y_left = 0
				b_max_Y_right = u + 1
				while b_max_Y_right - b_max_Y_left > 1:
					b_max_Y_middle = math.floor((b_max_Y_left + b_max_Y_right) / 2)
					if b_is_valid(y_star, x_star, u, b_max_Y_middle, tau):
						b_max_Y_left = b_max_Y_middle
					else:
						b_max_Y_right = b_max_Y_middle
				b_max_Y = b_max_Y_left
			# If (12) does not hold, we discard this case.
			if (u - b_max_X - b_max_Y) * b_xy > math.floor(P/2):
				continue
		# For n < 70, we use Lemmas B.3 and B.4 to find upped bounds on max_{X^*} b_U and max_{Y^*} b_U
		else:
			# First use Lemma B.3 to bound b_max_X and b_max_Y
			b_max_X = u 
			while not b_is_valid_small_n(x_star, y_star, u, b_max_X, tau, Delta):
				b_max_X -= 1
			b_max_Y = u 
			while not b_is_valid_small_n(y_star, x_star, u, b_max_Y, tau, Delta):
				b_max_Y -= 1
			if b_max_X < 0 or b_max_Y < 0:
				continue # No valid b for one of the two inequalities
			# Next, we use Lemma B.4 to bootstrap
			# If knowing b_U(x) <= |U|/2 would allow us to improve b_max_X, then we try to prove that b_U(x) <= |U|/2 in two different ways; same for b_max_Y
			b_UXstar = math.floor((u * b_xy + math.floor(P/2) - b_xy) * x_star / (x_min * y_min))
			b_UYstar = math.floor((u * b_xy + math.floor(P/2) - b_xy) * y_star / (x_min * y_min))
			potentially_improved_b_max_X = max(0, math.floor((math.floor(P/2) - max(0, b_xy - y_star) + b_UYstar) / y_star))
			potentially_improved_b_max_Y = max(0, math.floor((math.floor(P/2) - max(0, b_xy - x_star) + b_UXstar) / x_star))
			if b_max_X > potentially_improved_b_max_X:
				if b_max_X <= u/2:
					b_max_X = potentially_improved_b_max_X
				if F(y_star, u - math.floor((P - 2*max(0, b_xy - y_star) + 2*b_UYstar) / (2*y_star)), math.floor((x_star+y_star+Delta)/2)) > P - 2*max(0, b_xy - y_star) + b_UYstar:
					b_max_X = potentially_improved_b_max_X
			if b_max_Y > potentially_improved_b_max_Y:
				if b_max_Y <= u/2:
					b_max_Y = potentially_improved_b_max_Y
				if F(x_star, u - math.floor((P - 2*max(0, b_xy - x_star) + 2*b_UXstar) / (2*x_star)), math.floor((x_star+y_star+Delta)/2)) > P - 2*max(0,b_xy - x_star) + b_UXstar:
					b_max_Y = potentially_improved_b_max_Y
			# Check that (12) of Lemma 4.18 holds
			if (u - b_max_X - b_max_Y) * b_xy > math.floor(P/2):
				continue
			# Check that (13) of Lemma 4.18 holds
			if (u - b_max_X - b_max_Y) * b_xy > b_xy*(b_xy-1)/2 + b_xy * (x_bar_max + y_bar_max + min(b_max_X, b_max_Y)):
				continue 
		max_total_bad_edges = max(max_total_bad_edges, tau)
	return max_total_bad_edges

def no_counterexample(n, Delta, P): # Check if we can prove that G_{Delta, P} is empty, i.e. if tau <= 2*min(x_star, y_star, u) in all allowed configurations
	if not check_assumptions(n, Delta, P): # Check that assumptions of Lemmas 4.7, 4.13, and 4.15 hold; also compute eta along the way
		return False # If any of the assumptions don't hold, immediately fail
	for x_star in range(1, n-1):
		for y_star in range(x_star, n-x_star): # WLOG we may assume y_star >= x_star
			u = n - x_star - y_star
			tau = max_bad_edges(u,x_star, y_star, Delta, P) # Main argument: compute upper bound on number of edges not colored c*
			if tau > 2*min(x_star, y_star, u): # tau is too large; we are unable to prove G_{Delta, P} is empty
				return False
	return True # If we never returned False, we're done by Lemma 4.5

####### Section 2: Main Loop #######
####### Here we execute the algorithm outlined by Lemma B.1. #######
for n in range(3, N):
	# Preprocessing
	a = math.floor(n/3)
	b = math.floor((n+1)/3)
	c = math.floor((n+2)/3) # a,b,c are the sizes of the balanced tripartition
	g3.append(a*b*c+g3[a]+g3[b]+g3[c]) # Compute g3(n) recursively from its definition and append it to the list
	eta.append(eta_initial) # We will call check_assumptions to modify this if needed

	P = 4 * (n * (n**2 - ((n-1)%2+1)**2) / 24 - (g3[n]+1)) # Initial P = 4(d(n)-1)
	Delta_max = math.floor((max(0, n*(n-1)*(n+1)/3 - 8*(g3[n]+1)))**0.5) # Compute Delta_max according to (18)
	Delta = -1 # Initial Delta
	while True: # No limit on the number of iterations in Lemma B.1
		Delta_new = Delta_max
		while (Delta_new > Delta):
			if no_counterexample(n, Delta_new, P):
				break # We've found Delta^{(t)}
			Delta_new -= 1 # Otherwise, try again with Delta being 1 smaller
			eta[n]=eta_initial # Also reset eta[n] to eta_initial
		if Delta_new == Delta: # No Delta_new greater than the previous Delta works; procedure fails
			print("Procedure failed at n = " + str(n))
			break
		if Delta_new == Delta_max: # We showed what we needed; procedure succeeds
			break
		# If neither of the above occurs, update parameters and proceed to the next iteration
		Delta = Delta_new
		next_P = math.floor((n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - (Delta+1)**2) / 2)
		if next_P >= P: # No improvement on P; procedure fails
			print("Procedure failed at n = " + str(n))
			break
		P = next_P
	if n%10 == 0:
		print("Done up to n = "+str(n))

####### Section 3: bounding d(n) #######
####### Here we check to make sure d(n) <= c0 n log_2(n) for all 200 <= n <= 600, where c0 = 0.05891. This verifies Lemma B.5. #######
coeff_list = [0,0] + [(n * (n**2 - ((n-1)%2+1)**2) / 24 - g3[n]) / (n * math.log2(n)) for n in range(2,len(g3))]
max_coeff = max(coeff_list[200:])
max_coeff_index = coeff_list.index(max_coeff)
print("Biggest c0 needed: " + str(max_coeff) + ", occurs at: "+str(max_coeff_index))