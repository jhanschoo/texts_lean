import TextsLean.Basic

-- c.f. for ideals
#check Ideal.relIsoOfSurjective
#check Ideal.orderEmbeddingOfSurjective


-- c.f. for modules
#check Submodule.comapMkQRelIso

-- useful defs and lemmas
#check QuotientGroup.mk'

-- \begin{thm}[The Fourth or Lattice Isomorphism Theorem]\label{thm:3.20}
--   Let \(N\nsg G\), and let \(\calS=\B{A\leq G\colon N\leq A}\) Then there is a nondecreasing bijection \(F\colon \calS\to\setn[\calS]{A/N}[A]\colon A\mapsto A/N\). The following properties hold on \(A,B\in\calS\):
--   \begin{enumerate}
--     \item \(A\leq B\) if and only if \(A/N\leq B/N\). In particular, \(1\cong N/N\leq A/N\leq G/N\), and \(F\) is injective, and hence bijective.
--     \item If \(A\leq B\), then \(\abs{B:A}=\abs{B/N:A/N}\).
--     \item \(\ad{A,B}/N=\ad{A/N,B/N}\).
--     \item \(\p{A\sand B}/N=A/N\sand B/N\).
--     \item \(A\nsg G\) if and only if \(A/N\nsg G/N\).
--   \end{enumerate}
-- \end{thm}

-- \begin{prf}
--   The function is well-defined and surjective since \(A/N\) exists exactly when \(N\leq A\leq\CN_G\p{N}=G\). Checking the properties is straightforward and done as \Cref{xca:3.3.2}.
-- \end{prf}

-- \begin{xca}\label{xca:3.3.2}
--   Prove each property of \Cref{thm:3.20}.
-- \end{xca}

-- \begin{soln}~
--   \begin{enumerate}
--     \item Considering the natural projection homomorphism \(G\mapsto G/N\), we have \(A\sle B\) if and only if \(A/N\sle B/N\). By hypothesis, both \(A\) and \(B\) are subgroups of \(G\), so we can conclude \(A\leq B\) whenever \(A\sle B\); by the natural projection homomorphism, both \(A/N\) and \(B/N\) are subgroups of \(G/N\), hence also and \(A/N\leq B/N\) whenever \(A/N\sle B/N\).
--     \item The statement is equivalent to saying that there is a bijection between cosets of \(A\) in \(B\) and cosets of \(A/N\) in \(B/N\). By definition, for all \(bN\in B/N\), we have \(bN\setn[A/N]{aN}[aN]=\setn[A]{baN}[a]\). Consider \(\phi\colon bA\mapsto\setn[A]{baN}[a]\). If \(bA=b'A\), then \(b'=ba\) for some \(a\in A\), so that \(\setn[A]{b'a'N}[a']=\setn[A]{baa'N}[a']=\setn[A]{ba'N}[a']\). Hence the map is well-defined. It is clearly surjective, since \(b\in B\) was arbitrary. Moreover, the union of cosets of \(N\) in each element in the range of \(\phi\) is a coset of \(A\) itself, so that \(\setn[A]{baN}[a]=\setn[A]{b'aN}[a]\) implies \(bA=b'A\). Hence \(\phi\) is injective, and hence bijective.
--     \item This follows from \Cref{M-prop:2.9} and that \(aNbN=abN\) for all \(a,b\in G\).
--     \item This is immediate.
--     \item We have \(gNaN\p{g\inv N}=gag\inv N\) for all \(g\in G\) and \(a\in A\). Then \(gag\inv N\in\setn[A]{aN}[a]\) if and only if \(gag\inv\in A\), recalling that \(N\leq A\).
--   \end{enumerate}
-- \end{soln}
-- we have QuotientGroup.preimage_image_coe which is similar to the proof that the comap of a subgroup of the quotient group is itself a subgroup greater than the subgroup in the original group

#check Submodule.le_comap_mkQ
theorem le_comap_mk' [Group G] (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) : N ≤ Subgroup.comap (QuotientGroup.mk' N) H := by
  simpa using (Subgroup.comap_mono bot_le : (QuotientGroup.mk' N).ker ≤ Subgroup.comap (QuotientGroup.mk' N) H)

#check MonoidHom.range

#check Submodule.range_mkQ
theorem QuotientGroup.range_mk' [Group G] (N : Subgroup G) [N.Normal] : (QuotientGroup.mk' N).range = ⊤ :=
  (Subgroup.eq_top_iff' _).2 <| by rintro ⟨x⟩; exact ⟨x, rfl⟩

#check QuotientGroup.ker_mk'

#check Submodule.comap_map_mkQ
theorem QuotientGroup.comap_map_mk' [Group G] (N H : Subgroup G) [N.Normal] : Subgroup.comap (QuotientGroup.mk' N) (Subgroup.map (QuotientGroup.mk' N) H) = N ⊔ H := by simp [Subgroup.comap_map_eq, sup_comm]

-- Correspondence theorem for groups
def QuotientGroup.quotient {G : Type*} [Group G] (N : Subgroup G) [hn : N.Normal] : Subgroup (G ⧸ N) ≃o { H : Subgroup G // N ≤ H } where
  toFun H' := ⟨Subgroup.comap (QuotientGroup.mk' N) H', le_comap_quotient N _⟩
  invFun H := Subgroup.map (QuotientGroup.mk' N) H
  left_inv H' := Subgroup.map_comap_eq_self <| by simp [QuotientGroup.range_mk']
  right_inv := fun ⟨H, hH⟩ => Subtype.ext_val <| by simpa [QuotientGroup.comap_map_mk']
  map_rel_iff' := Subgroup.comap_le_comap_of_surjective <| QuotientGroup.mk'_surjective _
