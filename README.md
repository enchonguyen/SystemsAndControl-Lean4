# Systems and Control Theory in Lean 4

The purpose of this repository is to collect formalised definitions and theorems in the field of systems and control theory.

## Contents

### Linear Time-Invariant Systems in Discrete Time

#### `Solution.lean`
Consider the system
$$
\begin{align}
x(t+1) &= A x(t) + B u(t), \\
y(t) &= Cx(t) + Du(t).
\end{align}
$$
The solution to the initial value problem for a given $x(0) = x_0$ and $u$ is
$$
\begin{align}
x(t; x_0, u) &= A^t x_0 + \sum_{i = 0}^{t - 1} A^{t - i - 1} B u(i), \\
y(t; x_0, u) &= C A^t x_0 + \sum_{i = 0}^{t - 1} C A^{t - i - 1} B u(i) + D u(t).
\end{align}
$$

#### `AsymptoticStability.lean` and `LyapunovStability.lean`
The autonomous system $x(t+1) = Ax(t)$ is asymptotically stable if $x(t) \to 0$ as $t \to \infty$ for all initial conditions $x(0)$. The following are equivalent:
- the system $x(t+1) = Ax(t)$, where $A$ is a complex square matrix, is asymptotically stable;
- $\lim_{k \to \infty} A^k = 0$;
- the eigenvalues of $A$ have modulus less than 1;
- there exists a positive definite $P \succ 0$ such that $P - A^H P A \succ 0$.
