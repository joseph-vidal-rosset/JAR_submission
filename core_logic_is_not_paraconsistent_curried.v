Section CoreLogicNotParaconsistent.

Variables A B : Prop.

(* ------------------------------------------------------------------ *)
(*  1.1 DNS.1                                                         *)
(* ------------------------------------------------------------------ *)

Theorem dns1 :
  forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C).
Proof.
  intros D C H HD HK.
  apply HK.
  intro HA.
  apply H; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(*  1.2 DNS.2                                                         *)
(* ------------------------------------------------------------------ *)

Theorem dns2 :
  forall D C : Prop, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C).
Proof.
  intros D C H HD HK.
  apply HK.
  intro HA.
  exfalso.
  apply H; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(*  1.3 Inversion de DNS.1                                            *)
(* ------------------------------------------------------------------ *)

Theorem dns1_inv :
  forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C).
Proof.
  intros D C H HD HA.
  apply H; try assumption.
  intro HAC.
  apply HAC.
  exact HA.
Qed.

(* ------------------------------------------------------------------ *)
(*  1.4 DNS.1-anti                                                    *)
(* ------------------------------------------------------------------ *)

Theorem dns1_anti :
  forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C).
Proof.
  intros D C Hneg Hpos.
  apply Hneg.
  apply dns1_inv.
  exact Hpos.
Qed.

(* ------------------------------------------------------------------ *)
(*  1.5 Refutation de Claim 1                                         *)
(* ------------------------------------------------------------------ *)

Theorem claim1_refuted_full :
  ((((forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C)))
      -> (forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)))
    /\
    (forall D C : Prop, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C))
    /\
    ~(~A -> A -> B))
  -> False.
Proof.
  intro H.
  destruct H as [Hanti_builder Hrest].
  destruct Hrest as [Hdns2 Hclaim1].

  assert
    (Hpair :
      (forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C))).
  {
    split.
    - exact dns1.
    - exact dns1_inv.
  }

  assert
    (Hanti :
      forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)).
  {
    apply Hanti_builder.
    exact Hpair.
  }

  specialize (Hanti (~A) B).

  assert (HNAF : ~A -> A -> False).
  {
    intros HnA HA.
    exact (HnA HA).
  }

  assert (Hdns2inst : ~A -> ((A -> B) -> B) -> B).
  {
    apply Hdns2.
    exact HNAF.
  }

  apply (Hanti Hclaim1).
  exact Hdns2inst.
Qed.

(* ------------------------------------------------------------------ *)
(*  2. Refutation de Claim 2                                          *)
(* ------------------------------------------------------------------ *)

Theorem claim2_refuted_full :
  ((((forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C)))
      -> (forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)))
    /\
    (forall D C : Prop, (D -> A -> False) -> (D -> ((A -> C) -> C) -> C))
    /\
    ~(~A -> A -> ~B))
  -> False.
Proof.
  intro H.
  destruct H as [Hanti_builder Hrest].
  destruct Hrest as [Hdns2 Hclaim2].

  assert
    (Hpair :
      (forall D C : Prop, (D -> A -> C) -> (D -> ((A -> C) -> C) -> C)) /\
      (forall D C : Prop, (D -> ((A -> C) -> C) -> C) -> (D -> A -> C))).
  {
    split.
    - exact dns1.
    - exact dns1_inv.
  }

  assert
    (Hanti :
      forall D C : Prop, ~(D -> A -> C) -> ~(D -> ((A -> C) -> C) -> C)).
  {
    apply Hanti_builder.
    exact Hpair.
  }

  specialize (Hanti (~A) (~B)).

  assert (HNAF : ~A -> A -> False).
  {
    intros HnA HA.
    exact (HnA HA).
  }

  assert (Hdns2inst : ~A -> ((A -> ~B) -> ~B) -> ~B).
  {
    apply Hdns2.
    exact HNAF.
  }

  apply (Hanti Hclaim2).
  exact Hdns2inst.
Qed.

End CoreLogicNotParaconsistent.