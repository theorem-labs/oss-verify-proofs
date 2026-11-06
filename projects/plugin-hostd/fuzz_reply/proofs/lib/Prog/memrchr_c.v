From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition MEMRCHR : Z := 0x1d67c.

Fixpoint rfind_byte (c : Z) (l : list byte) : option nat :=
  match l with
  | [] => None
  | b :: l' =>
      match rfind_byte c l' with
      | Some i => Some (S i)
      | None => if bv_unsigned b =? c then Some 0%nat else None
      end
  end.

Lemma rfind_byte_None : forall c l, rfind_byte c l = None ->
  forall j b, nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l; induction l as [|x l IH]; intros H j b Hn; [destruct j; discriminate|].
  cbn in H. destruct (rfind_byte c l) eqn:E; [discriminate|].
  destruct (Z.eqb_spec (bv_unsigned x) c) as [Ex|Nx]; [discriminate|].
  destruct j as [|j]; cbn in Hn; [injection Hn as <-; exact Nx | exact (IH eq_refl j b Hn)].
Qed.

Lemma rfind_byte_Some : forall c l i, rfind_byte c l = Some i ->
  (i < length l)%nat /\ (exists b, nth_error l i = Some b /\ bv_unsigned b = c) /\
  (forall j b, (i < j)%nat -> nth_error l j = Some b -> bv_unsigned b <> c).
Proof.
  intros c l; induction l as [|x l IH]; intros i H; cbn in H; [discriminate|].
  destruct (rfind_byte c l) as [i'|] eqn:E.
  - injection H as <-. destruct (IH i' eq_refl) as (Hl & (b & Hn & Hb) & Hmax).
    split; [cbn; lia|]. split; [exists b; split; [exact Hn | exact Hb]|].
    intros [|j] b2 Hj Hn2; [lia|]. cbn in Hn2. apply (Hmax j b2); [lia | exact Hn2].
  - destruct (Z.eqb_spec (bv_unsigned x) c) as [Ex|Nx]; [|discriminate]. injection H as <-.
    split; [cbn; lia|]. split; [exists x; split; [reflexivity | exact Ex]|].
    intros [|j] b2 Hj Hn2; [lia|]. cbn in Hn2. exact (rfind_byte_None c l E j b2 Hn2).
Qed.

Lemma rfind_byte_snoc_hit : forall c l x, bv_unsigned x = c -> rfind_byte c (l ++ [x]) = Some (length l).
Proof.
  intros c l x H; induction l as [|y l IH].
  - cbn. rewrite (proj2 (Z.eqb_eq _ _) H). reflexivity.
  - cbn [app rfind_byte length]. rewrite IH. reflexivity.
Qed.

Lemma rfind_byte_snoc_miss : forall c l x, bv_unsigned x <> c -> rfind_byte c (l ++ [x]) = rfind_byte c l.
Proof.
  intros c l x H; induction l as [|y l IH].
  - cbn. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
  - cbn [app rfind_byte]. rewrite IH. reflexivity.
Qed.

Definition memrchr_res (A c n : Z) (buf : list byte) : Z :=
  match rfind_byte c (firstn (Z.to_nat n) buf) with Some i => A + Z.of_nat i | None => 0 end.

Definition memrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Definition memrchr_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte),
    bytes_at rsegs m (bv_unsigned a0) buf ->
    bv_unsigned a2 <= Z.of_nat (length buf) ->
    mem_inv rsegs m ->
    evt rsegs (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MEMRCHR) fc None m (seg_rom rsegs)).
