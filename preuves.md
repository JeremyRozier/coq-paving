# Preuves

## Preuves 1D

$$\exists c \in X_\tau \Longleftrightarrow \exists d \in X_\tau \; \exists n \in \mathbb{N} \; \forall m \in \mathbb{Z} \; d_{m+n} = d_m$$
\
Soit $c \in X\tau$ \
On sait que $\mathbb{Z}$ n'est pas fini et que $\tau$ est fini.
\
Donc il existe $t \in \tau$ tel que $c^{-1}(t)$ n'est pas fini.\
Soit $m' \in c^{-1}(t)$, il existe $n \in \mathbb{N}$ tel que $c_{m'+n} = c_m'$.\
Soit $d \in \tau^{\mathbb{Z}}$ tel que :
$$\forall m\in \mathbb{Z} \; \forall k \in [\![0, n-1]\!]\; m \equiv k [n]\;d_m = c_{m' + k}
$$
En effet pour tout $m \in [\![m', m'+n-2]\!]$, on a en particulier $c_m$ qui est compatible à droite avec $c_{m+1}$ puisque $c \in X\tau$. On en déduit que $\forall m\in \mathbb{Z}\; \forall k \in [\![0, n-2]\!]\; m = k[n]$ $d_m$ est compatible à droite avec $d_{m+1}$. De plus $d_{m'+n-1}$ est compatible à droite avec $d_{m'+n}$ puisque par définition de $d$ on a : $d_{m'+n-1} = c_{m'-1}$ et $d_{m'+n} = c_{m'}$ et que par validité de $c$ on a $c_{m'-1}$ qui est compatible à droite avec $c_{m'}$. Donc on a $\forall m\in \mathbb{Z}\; \forall k \in [\![0, n-1]\!]\; m = k[n]\;d_m$ qui est compatible à droite avec $d_{m+1}$.
\
Ainsi on a bien $d \in X\tau$.
\
Donc on a trouvé une configuration $d \in X_{\tau}$ et $n \in \mathbb{N}$ tels que:
$$\forall m\in \mathbb{Z}\;d_{m+n} = d_m$$
c'est à dire $d \in X_{\tau}$ est périodique.
\
Réciproquement s'il existe $d \in X_\tau$ tel que $\exists n \in \mathbb{N} \; \forall m \in \mathbb{Z} \; d_{m+n} = d_m$ alors $d\in X_\tau$.
\
On a donc montré l'équivalence.
