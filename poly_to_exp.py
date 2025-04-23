import math

N = 1000
g3 = [0,0,0] # Start by initializing g3(0)=g3(1)=g3(2)=0
eta = [0,0,0]

def bip(x):
	return math.ceil(x/2)*math.floor(x/2)

def F(A, B, C):
	# WLOG assume that A >= B
	if A < B:
		A, B = B, A
	t = math.ceil((A + B) / C)
	last_piece = A + B - (t - 1) * C  # Compute a_t + b_t
	if (A - B) / t > (A + B) - (t - 1) * C:
		D_prime = (A + B) - (t - 1) * C
		D = ((A - B) - D_prime) / (t - 1)  # Using (t - 1) * D + D' = A - B
	else:
		D = D_prime = (A - B) / t
	# ai * bi = ((ai + bi)^2 - (ai - bi)^2) / 4
	return A * B - (t - 1) * (C * C - D * D) / 4 - (last_piece ** 2 - D_prime ** 2) / 4

def u_is_large_enough(x, y, u, b, n): # Checking first equation of assumption of Lemma 1.10
	x_diff = max(x - b/y - u, 0)
	y_diff = max(y - b/x - u, 0)
	return x*(y_diff**2) + y*(x_diff**2) + (x-y)**2 <= n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - 4*b


def check_assumptions(n, Delta, bad_triangles):
	if math.ceil(12*g3[n] / (n*(n-1))) < math.ceil(n/2):
		return False # Assumption of Lemma 1.6 is violated
	for s in range(1, n-1):
		for t in range(max(1, math.ceil(n/2)-s), n-s): # Generate pairs (s,t) with ceil(n/2) <= s+t <= n-1
			if abs(s-t) > Delta:
				continue # If |s-t| > Delta(n) then we discard this case
			if s*t + bip(n-1-s-t) < g3[n]-g3[n-1]+1: # v can't be in enough monochromatic triangles, so we discard this case
				continue
			if s*t < 8*math.floor(bad_triangles/2): # eta <= 1/8 doesn't hold. We next look for a contradiction to 3. of Lemma 1.6.
				min_d1_plus_d2 = n-1 # We now compute S = min_d1_plus_d2 satisfying 3. of Lemma 1.6
				for d1 in range(1, s+t+1):
					for d2 in range(1, d1+1):
						if bip(d1) + math.floor((n-1-d1)/d2) * bip(d2) + bip((n-1-d1)%d2) > g3[n]-g3[n-1]:
							min_d1_plus_d2 = min(min_d1_plus_d2, d1+d2)
							break # Looking for smallest possible satisfying the equation, so no point looking any further
				if min_d1_plus_d2 > 8/9*n:
					continue # If point 3. of Lemma 1.6 is violated then we discard this case
				eta[n] = max(eta[n], math.floor(bad_triangles/2)/(s*t)) # Otherwise we update eta
			if F(s, t - math.floor(bad_triangles/(2*s)), math.floor((s+t+Delta)/2)) <= bad_triangles:
				return False # Assumption of Lemma 1.8 is violated
			for k in range(math.floor(bad_triangles/2) + 1):
				if not u_is_large_enough(s, t, n-s-t, k, n):
					continue # If even w=n-s-t does not work, then no w works
				w_left = 0
				w_right = n - s - t + 1 # Binary search for w
				while(w_right - w_left > 1):
					w_middle = math.floor((w_left+w_right)/2)
					if u_is_large_enough(s, t, w_middle-1, k, n):
						w_right = w_middle
					else:
						w_left = w_middle
				w = w_left
				if F(s, w - (math.floor(bad_triangles/2) - k - w*k/t)/s, math.floor((s+t+Delta)/2)) <= bad_triangles - 2*k + w*k/t:
					return False # First inequality of assumption of Lemma 1.10
				if F(w, s - (math.floor(bad_triangles/2) - k - w*k/t)/w, math.floor((s+t+Delta)/2)) <= bad_triangles - 2*k + w*k/t:
					return False # Second inequality of assumption of Lemma 1.10
	return True

# Helper functions to find b_max_from_x and b_max_from_y
def b_is_valid(x_prime, y_prime, u, b, tau):
	n = x_prime + y_prime + u
	return (u-b)*y_prime + bip(x_prime-1) + bip(b) + tau - b >= g3[n]-g3[n-1]+1

def b_is_valid_small_n(x_prime, y_prime, u, b, tau, Delta):
	n = x_prime + y_prime + u
	b_prime = max(0, y_prime - (u-b+Delta)) # This is a lower bound on b'
	if (u - b) * (y_prime - b_prime) + bip(x_prime-1) + bip(b) + bip(b_prime) + tau - b - b_prime >= g3[n]-g3[n-1]+1:
		return True
	b_prime = min(y_prime, y_prime - (u-b-Delta)); #This is an upper bound on b'
	if (u - b) * (y_prime - b_prime) + bip(x_prime-1) + bip(b) + bip(b_prime) + tau - b - b_prime >= g3[n]-g3[n-1]+1:
		return True
	return False # Since the LHS is convex, if LHS is not big enough at the endpoints, then it is always not big enough.

def max_bad_edges(u, x_prime, y_prime, Delta, bad_triangles):
	n = u + x_prime + 		y_prime
	if x_prime + y_prime < math.ceil(n/2): # Avoid entering the for loop in these cases
		return 0
	max_total_bad_edges = 0
	for b_xy in range(math.floor(bad_triangles/2)+1):
		M_star = min(math.floor((math.floor(bad_triangles/2) - b_xy) / ((1-eta[n]) * (n/4-Delta/2)) * (1+1/u)), x_prime + y_prime - math.ceil(n/2))
		if abs(x_prime-y_prime) > M_star + Delta:
			return max_total_bad_edges # First part of Lemma 1.11 is violated, and since M_star is non-increasing in b_xy, the same will be true of larger b_xy
		x_star_max = M_star + min(x_prime - y_prime + Delta, 0)
		y_star_max = M_star + min(y_prime - x_prime + Delta, 0)
		x_min = x_prime - x_star_max
		y_min = y_prime - y_star_max
		if x_min * max((1-eta[n]) * y_min - u, 0)**2 + y_min * max((1-eta[n]) * x_min - u, 0)**2 > n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - 4*b_xy:
			continue # Equation (6) violated 
		if x_min * max((1-eta[n]) * u - y_prime, 0)**2 + y_min * max((1-eta[n]) * u - x_prime, 0)**2 > n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - 4*b_xy:
			continue # Equation (7) violated
		coeff_b_xy = 1 + x_star_max / x_min + y_star_max / y_min + u * (x_prime + y_prime) / (x_min * y_min)
		coeff_badtriangles = (1 + x_star_max / x_min + y_star_max / y_min) * (1/x_min + 1/y_min + 1/u)
		tau = math.floor(coeff_b_xy * b_xy + coeff_badtriangles * (math.floor(bad_triangles/2) - b_xy) + x_star_max * y_star_max)
		# Two different strategies depending on whether n>=70 or n<70
		# For n>=70, if Equation (9) holds and either b_max_from_x or b_max_from_y is undefined or Equation (10) fails to hold, then we discard this case.
		if n >= 70 and bip(x_prime) + bip(y_prime) + bip(u) + tau <= g3[n]-g3[n-1]:
			# Binary search to find b_max_from_x and b_max_from_y
			# Note that the LHS in equation (8) is not monotone in b. However, it is convex, so it suffices to do the following:
			# First, test b = u. If it works, we're done.
			# If b = u doesn't work, test b = 0. If that doesn't work, then by convexity, no b works, and we discard this case.
			# If b = u doesn't work while b = 0 does, then we do binary search to find the maximum b that works.
			if b_is_valid(x_prime, y_prime, u, u, tau):
				b_max_from_x = u
			else:
				if not b_is_valid(x_prime, y_prime, u, 0, tau):
					continue # Discard this case
				b_max_from_x_left = 0
				b_max_from_x_right = u + 1
				while b_max_from_x_right - b_max_from_x_left > 1:
					b_max_from_x_middle = math.floor((b_max_from_x_left + b_max_from_x_right) / 2)
					if b_is_valid(x_prime, y_prime, u, b_max_from_x_middle, tau):
						b_max_from_x_left = b_max_from_x_middle
					else:
						b_max_from_x_right = b_max_from_x_middle
				b_max_from_x = b_max_from_x_left
			# Same idea to find b_max_from_y
			if b_is_valid(y_prime, x_prime, u, u, tau):
				b_max_from_y = u
			else:
				if not b_is_valid(y_prime, x_prime, u, 0, tau):
					continue # Discard this case
				b_max_from_y_left = 0
				b_max_from_y_right = u + 1
				while b_max_from_y_right - b_max_from_y_left > 1:
					b_max_from_y_middle = math.floor((b_max_from_y_left + b_max_from_y_right) / 2)
					if b_is_valid(y_prime, x_prime, u, b_max_from_y_middle, tau):
						b_max_from_y_left = b_max_from_y_middle
					else:
						b_max_from_y_right = b_max_from_y_middle
				b_max_from_y = b_max_from_y_left
			# Eq (9) holds, so if Eq (10) does not, we discard this case.
			if (u - b_max_from_x - b_max_from_y) * b_xy > math.floor(bad_triangles/2):
				continue
		# For n < 70, we don't use Equation (9) or binary search; rather, we find a valid b_max_from_x and b_max_from_y directly.
		else:
			b_max_from_x = u 
			while not b_is_valid_small_n(x_prime, y_prime, u, b_max_from_x, tau, Delta):
				b_max_from_x -= 1
			b_max_from_y = u 
			while not b_is_valid_small_n(y_prime, x_prime, u, b_max_from_y, tau, Delta):
				b_max_from_y -= 1
			if b_max_from_x < 0 or b_max_from_y < 0:
				continue # No valid b for one of the two inequalities
			# Bootstrapping step: if knowing b_U(x) <= |U|/2 would allow us to improve b_max_from_x, then we try to prove that b_U(x) <= |U|/2 in two different ways.
			b_UXprime = math.floor((u * b_xy + math.floor(bad_triangles/2) - b_xy) * x_prime / (x_min * y_min))
			b_UYprime = math.floor((u * b_xy + math.floor(bad_triangles/2) - b_xy) * y_prime / (x_min * y_min))
			potentially_improved_b_max_from_x = max(0, math.floor((math.floor(bad_triangles/2) - max(0, b_xy - y_prime) + b_UYprime) / y_prime))
			potentially_improved_b_max_from_y = max(0, math.floor((math.floor(bad_triangles/2) - max(0, b_xy - x_prime) + b_UXprime) / x_prime))
			if b_max_from_x > potentially_improved_b_max_from_x:
				if b_max_from_x <= u/2:
					b_max_from_x = potentially_improved_b_max_from_x
				if F(y_prime, u - math.floor((bad_triangles - 2*max(0, b_xy - y_prime) + 2*b_UYprime) / (2*y_prime)), math.floor((x_prime+y_prime+Delta)/2)) > bad_triangles - 2*max(0, b_xy - y_prime) + b_UYprime:
					b_max_from_x = potentially_improved_b_max_from_x
			if b_max_from_y > potentially_improved_b_max_from_y:
				if b_max_from_y <= u/2:
					b_max_from_y = potentially_improved_b_max_from_y
				if F(x_prime, u - math.floor((bad_triangles - 2*max(0, b_xy - x_prime) + 2*b_UXprime) / (2*x_prime)), math.floor((x_prime+y_prime+Delta)/2)) > bad_triangles - 2*max(0,b_xy - x_prime) + b_UXprime:
					b_max_from_y = potentially_improved_b_max_from_y
			# If Eq (10) does not hold, we discard this case.
			if (u - b_max_from_x - b_max_from_y) * b_xy > math.floor(bad_triangles/2):
				continue
			if (u - b_max_from_x - b_max_from_y) * b_xy > b_xy*(b_xy-1)/2 + b_xy * (x_star_max + y_star_max + min(b_max_from_x, b_max_from_y)):
				continue # We can recolor all crossing edges to color c without losing monochromatic triangles
		max_total_bad_edges = max(max_total_bad_edges, tau)
	return max_total_bad_edges

def no_counterexample(n, Delta, bad_triangles):
	if not check_assumptions(n, Delta, bad_triangles): # Check if Lemmas 1.6, 1.8, and 1.10 work; also compute eta along the way
		return False
	for x_prime in range(1, n-1):
		for y_prime in range(x_prime, n-x_prime): # WLOG we may assume y_prime >= x_prime
			u = n - x_prime - y_prime;
			tau = max_bad_edges(u,x_prime, y_prime, Delta, bad_triangles) # Main argument
			if tau > 2*min(x_prime, y_prime, u): # If this never happens, we're done by Lemma 1.12
				return False
	return True

# Main loop
for n in range(3, N):
	# Preprocessing
	a = math.floor(n/3)
	b = math.floor((n+1)/3)
	c = math.floor((n+2)/3) # a,b,c are the sizes of the balanced tripartition
	g3.append(a*b*c+g3[a]+g3[b]+g3[c]) # Compute g3(n) recursively and append it to the list
	eta.append(0.125) # We will call check_assumptions to modify this if needed

	bad_triangles = 4 * (n * (n**2 - ((n-1)%2+1)**2) / 24 - (g3[n]+1)) # Initial M_{bad triangles}
	Delta_max = math.floor((max(0, n*(n-1)*(n+1)/3 - 8*(g3[n]+1)))**0.5) # Compute Delta_max
	Delta = -1 # Initial Delta
	while True: # No limit on the number of iterations in Corollary 1.3
		Delta_new = Delta_max
		while (Delta_new > Delta):
			if no_counterexample(n, Delta_new, bad_triangles):
				break # We've found Delta^{(t)}
			Delta_new -= 1 # Otherwise, try again with Delta being 1 smaller
			eta[n]=0.125 # Also reset eta[n] to 1/8
		if Delta_new == Delta: # No Delta_new greater than the previous Delta works. Procedure fails.
			print("Procedure failed at n = " + str(n))
			break
		if Delta_new == Delta_max: # We showed what we needed; procedure succeeds
			break
		# If neither of the above occurs, update parameters and proceed to the next iteration.
		Delta = Delta_new
		next_bad_triangles = math.floor((n*(n+1)*(n-1)/3 - 8*(g3[n]+1) - (Delta+1)**2) / 2)
		if next_bad_triangles >= bad_triangles: # No improvement on M_{bad triangles}. Procedure fails.
			print("Procedure failed at n = " + str(n))
			break
		bad_triangles = next_bad_triangles
	if n%10 == 0:
		print("Done up to n = "+str(n))

# Check to make sure d(n) <= c n log_2(n) for all 100 <= n <= N, where c = 0.06.
coeff_list = [0,0] + [(n * (n**2 - ((n-1)%2+1)**2) / 24 - g3[n]) / (n * math.log2(n)) for n in range(2,len(g3))]
max_coeff = max(coeff_list[100:])
max_coeff_index = coeff_list.index(max_coeff)
print("Biggest c1 needed: " + str(max_coeff) + ", occurs at: "+str(max_coeff_index))