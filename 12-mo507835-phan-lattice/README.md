# 12. Phan Three-Layer Lattice $C_4$-Free Density

Verified partial proof, exact optimal $n = 4$ construction, and periodic search for Veronica Phan's lattice edge-density conjecture ([MathOverflow #507835](https://mathoverflow.net/questions/507835), related to Erdos Problem #86).

Four-cycle incidence counting proves asymptotic $C_4$-free density $\le 3/4$ for all $n \ge 2$, settling Phan's bound $\frac{1}{2} + \frac{1}{2\sqrt{n}}$ completely for $n = 2, 3, 4$, paired with an explicit $\mathbb{F}_2^2$-parity construction attaining density $3/4$ in $n = 4$. The conjecture remains open for $n \ge 5$, where a periodic CPU annealing verifier and a PyTorch GPU Colab notebook explore quotients targeting $\approx 0.723607$.

- [Proof note and periodic tables](NOTES.md)
- [CPU periodic verifier and $n = 4$ construction ⬜](phan_periodic.py)
- [PyTorch GPU Colab notebook ($n = 5$ search)](colab_phan_gpu.ipynb)

Run `python3 phan_periodic.py --dimensions 2 3 4 --periods 3 4 6`.
