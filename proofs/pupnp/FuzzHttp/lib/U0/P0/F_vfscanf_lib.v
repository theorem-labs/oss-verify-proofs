(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt ScanIntProps.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib F_errno_location.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib F_intscan_J.
Import ListNotations.
Open Scope Z_scope.

Definition VFSCANF : Z := 0x1fff4.
Definition VF_DEPTH : Z := 720.
Notation ERRNO tp := (bv_unsigned tp - 164)%Z (only parsing).

Fixpoint fmt_enc (l : list Z) (ds : list sdir) : Prop :=
  match ds with
  | [] => match l with 0 :: _ => True | _ => False end
  | SD :: ds' => match l with 37 :: 100 :: l' => fmt_enc l' ds' | _ => False end
  | SW :: ds' => match l with 32 :: l' => match l' with c :: _ => c <> 32 /\ ~ (9 <= c <= 13) | [] => False end /\ fmt_enc l' ds' | _ => False end
  | SL ch :: ds' => match l with c :: l' => c = ch /\ 32 < c < 128 /\ c <> 37 /\ fmt_enc l' ds' | _ => False end
  end.
Fixpoint dlen (ds : list sdir) : nat :=
  match ds with [] => 0 | SD :: ds' => 2 + dlen ds' | _ :: ds' => 1 + dlen ds' end%nat.
Fixpoint nconv (ds : list sdir) : Z :=
  match ds with [] => 0 | SD :: ds' => 1 + nconv ds' | _ :: ds' => nconv ds' end.

Definition FMTL_VERSION : list Z := [37; 100; 32; 46; 32; 37; 100; 0].
Definition FMTL_STATUS : list Z := [37; 100; 32; 46; 32; 37; 100; 32; 37; 100; 0].
Lemma fmt_enc_version : fmt_enc FMTL_VERSION FMT_VERSION. Proof. cbn. repeat split; lia. Qed.
Lemma fmt_enc_status : fmt_enc FMTL_STATUS FMT_STATUSLINE. Proof. cbn. repeat split; lia. Qed.

Definition nthP (P1 P2 P3 : Z) (na : Z) : Z := if na =? 0 then P1 else if na =? 1 then P2 else P3.

Definition ERRNOA : Z := 0x3b77c.

Definition vf_FP (q : Z) (P1 P2 P3 : Z) : list (Z * Z) :=
  [(q - VF_DEPTH, q); (q + 8, q + 8 + 232); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (ERRNOA, ERRNOA + 4)]%Z.

Open Scope bv_scope.

Definition vlow (apw j16 j32 j40 : word) (mt : Z) (j56 j64 : word) (j72 : list byte) : list cell :=
  [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 ssp_guard); C8 j16; C8 apw; C8 j32; C8 j40; C8 (Z_to_bv 64 mt); C8 j56; C8 j64; CB 40 j72].
Definition vhi (canary ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 canary; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition vinv (ra : word) (q : Z) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word) (m0 : word -> option byte)
    (T : Z) (txt : list Z) (canary : word) (P1 P2 P3 FA : Z) (fmtl : list Z) (w3n : nat) (ap3w : word)
    (na mt : Z) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ munch (vf_FP q P1 P2 P3) m0 m /\ wmono rsegs m0 m
  /\ (exists j16 j32 j40 j56 j64 j72, rw_cells rsegs m (q + -480) (vlow (Z_to_bv 64 (q + 320 + 8 * na)) j16 j32 j40 mt j56 j64 j72))
  /\ (exists scs, rw_cells rsegs m (q + -368) [CB 256 scs])
  /\ rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e)
  /\ stk rsegs m (q - VF_DEPTH) (q + -480)
  /\ bytes_at rsegs m T (zbytes txt) /\ ssp_cells m canary
  /\ (exists ev : word, rw_cells rsegs m ERRNOA [C4 ev])
  /\ rw_cells rsegs m (q + 320) [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w]
  /\ (exists (v1 v2 : word) (v3 : list byte), rw_cells rsegs m P1 [C4 v1] /\ rw_cells rsegs m P2 [C4 v2] /\ rw_cells rsegs m P3 [CB w3n v3])
  /\ bytes_at rsegs m FA (zbytes fmtl).

Definition vf_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (T : Z) (txt : list Z) (canary : word) (P1 P2 P3 : Z) (w3n : nat) (ap3w : word) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte) (ev v1 v2 : word) (v3 : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (vf_FP q P1 P2 P3) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - VF_DEPTH) q
    /\ rw_cells rsegs m' (q + 8) [CB 232 junk]
    /\ bytes_at rsegs m' T (zbytes txt) /\ ssp_cells m' canary
    /\ rw_cells rsegs m' ERRNOA [C4 ev]
    /\ rw_cells rsegs m' (q + 320) [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w]
    /\ rw_cells rsegs m' P1 [C4 v1] /\ rw_cells rsegs m' P2 [C4 v2] /\ rw_cells rsegs m' P3 [CB w3n v3].

Definition LH_at (ra : word) (q : Z) (gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (T p : Z) (txt : list Z) (canary : word) (P1 P2 P3 FA : Z) (fmtl : list Z) (W3num : Z) (w3n : nat) (ap3w : word) (fuel : nat) (ds : list sdir) : Prop :=
  forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word),
    vinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 T txt canary P1 P2 P3 FA fmtl w3n ap3w na mt m ->
    rw_cells rsegs m (q + 8) (rf_cells T co f ssJ) -> RFJ T txt p ssJ co k c f -> (0 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat i) fmtl) ds -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + nconv ds <= W3num)%Z ->
    vfs fuel ds f mt = Some r ->
    evt rsegs (vf_post ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T txt canary P1 P2 P3 w3n ap3w r)
      (MS (mkR x1 (Z_to_bv 64 (q + -480)) gp tp x5 x6 x7 (Z_to_bv 64 (q + 8)) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 31) (Z_to_bv 64 37) (Z_to_bv 64 (FA + i)) x22 x23 (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x200c4) fc None m (seg_rom rsegs)).

Lemma skipn_cons_znth : forall (l : list Z) n a l', skipn n l = a :: l' -> znth l (Z.of_nat n) = a /\ l' = skipn (S n) l /\ (n < length l)%nat.
Proof.
  intros l n a l' H.
  assert (Hn : (n < length l)%nat).
  { destruct (Nat.lt_ge_cases n (length l)) as [L|L]; [exact L|]. rewrite skipn_all2 in H by lia. discriminate H. }
  split; [|split; [|exact Hn]].
  - unfold znth. destruct (Z.ltb_spec0 (Z.of_nat n) 0); [lia|]. rewrite Nat2Z.id.
    pose proof (firstn_skipn n l) as E. rewrite H in E. rewrite <- E. rewrite app_nth2 by (rewrite firstn_length; lia).
    rewrite firstn_length. replace (n - Nat.min n (length l))%nat with 0%nat by lia. reflexivity.
  - replace (S n) with (1 + n)%nat by lia. rewrite <- skipn_skipn, H. reflexivity.
Qed.
Lemma nconv_nonneg : forall ds, (0 <= nconv ds)%Z.
Proof. induction ds as [|[| |c] ds IH]; cbn; lia. Qed.

Lemma ws_loop_stdio : forall n f c f1, is_ws_loop n f = Some (c, f1) -> sh_stdio f1 = sh_stdio f.
Proof.
  induction n as [|n IH]; intros f c f1 H; [discriminate H|]. cbn [is_ws_loop] in H.
  pose proof (stdio_getc f) as S. destruct (sh_getc f) as [c0 f0]. cbn [snd] in S.
  destruct (m_isspace c0). - rewrite <- S. eapply IH. exact H. - injection H as <- <-. exact S.
Qed.
Lemma dig_loop_stdio : forall n b c f c1 f1, is_dig_loop n b c f = Some (c1, f1) -> sh_stdio f1 = sh_stdio f.
Proof.
  induction n as [|n IH]; intros b c f c1 f1 H; [discriminate H|]. cbn [is_dig_loop] in H.
  destruct (digval c <? b)%Z.
  - pose proof (stdio_getc f) as S. destruct (sh_getc f) as [c0 f0]. cbn [snd] in S. rewrite <- S. eapply IH. exact H.
  - injection H as <- <-. reflexivity.
Qed.
Lemma digits_stdio : forall n b c f f1, is_digits n b c f = Some f1 -> sh_stdio f1 = sh_stdio f.
Proof.
  intros n b c f f1 H. unfold is_digits in H. destruct (is_dig_loop n b c f) as [[c2 f2]|] eqn:E; [|discriminate H].
  injection H as <-. rewrite stdio_unget. eapply dig_loop_stdio. exact E.
Qed.
Lemma intscan_stdio : forall n b pk f f1, intscan n b pk f = Some f1 -> sh_stdio f1 = sh_stdio f.
Proof.
  intros n b pk f f1 H. unfold intscan in H.
  destruct (is_ws_loop n f) as [[c0 f0]|] eqn:E0; [|discriminate H]. pose proof (ws_loop_stdio _ _ _ _ E0) as S0.
  assert (S1 : forall c2 f2, (if ((c0 =? 43) || (c0 =? 45))%Z then sh_getc f0 else (c0, f0)) = (c2, f2) -> sh_stdio f2 = sh_stdio f).
  { intros c2 f2 E. destruct ((c0 =? 43) || (c0 =? 45))%Z. - pose proof (stdio_getc f0) as S. rewrite E in S. cbn in S. congruence. - injection E as <- <-. exact S0. }
  destruct (if ((c0 =? 43) || (c0 =? 45))%Z then sh_getc f0 else (c0, f0)) as [c2 f2]. specialize (S1 _ _ eq_refl).
  destruct ((b =? 16) && (c2 =? 48))%Z.
  - pose proof (stdio_getc f2) as S3. destruct (sh_getc f2) as [c3 f3]. cbn [snd] in S3.
    destruct (Z.lor c3 32 =? 120)%Z.
    + pose proof (stdio_getc f3) as S4. destruct (sh_getc f3) as [c4 f4]. cbn [snd] in S4.
      destruct (16 <=? digval c4)%Z.
      * injection H as <-. unfold nz. destruct (pk =? 0)%Z; cbn [negb]; rewrite ?stdio_lim0, ?stdio_unget, ?stdio_unget; congruence.
      * rewrite (digits_stdio _ _ _ _ _ H). congruence.
    + rewrite (digits_stdio _ _ _ _ _ H). congruence.
  - destruct (b <=? digval c2)%Z.
    + injection H as <-. rewrite stdio_lim0, stdio_unget. exact S1.
    + rewrite (digits_stdio _ _ _ _ _ H). exact S1.
Qed.
Lemma RFJ_k0 : forall T txt p J co k c f, RFJ T txt p J co k c f -> RFJ T txt p J co 0 c f.
Proof.
  intros T txt p J co k c f (OK & Rc & CC & KM & NS & SS). unfold RFJ. split; [exact OK|]. split; [exact Rc|]. split; [exact CC|].
  split; [intros _; lia|]. split; [exact NS | exact SS].
Qed.

Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.

Definition hidden (P : Prop) := P.
Ltac stash H := lazymatch type of H with hidden _ => idtac | ?T => change T with (hidden T) in H end.
Ltac unstash := unfold hidden in *.

Definition conv8 (c : cell) : cell :=
  match c with CB 8 b => C8 (le_bytes_to_word b) | CB 4 b => C4 (le_bytes_to_word b) | _ => c end.
Fixpoint conv_sel (idxs : list nat) (i : nat) (cs : list cell) : list cell :=
  match cs with [] => [] | c :: cs' => (if existsb (Nat.eqb i) idxs then conv8 c else c) :: conv_sel idxs (S i) cs' end.
Lemma rw_cells_conv8 : forall m A pre c post, rw_cells rsegs m A (pre ++ c :: post) -> rw_cells rsegs m A (pre ++ conv8 c :: post).
Proof.
  intros m A pre c post H. destruct c as [v|v|v|b|n bs]; try exact H.
  destruct n as [|[|[|[|[|[|[|[|[|n]]]]]]]]];
    first [ exact H | exact (rw_cells_CB_C4 rsegs m A pre bs post H) | exact (rw_cells_CB_C8 rsegs m A pre bs post H) ].
Qed.
Lemma rw_cells_conv_sel : forall idxs m A cs pre i,
  rw_cells rsegs m A (pre ++ cs) -> rw_cells rsegs m A (pre ++ conv_sel idxs i cs).
Proof.
  intros idxs m A cs. induction cs as [|c cs IH]; intros pre i H; cbn [conv_sel]; [exact H|].
  assert (H1 : rw_cells rsegs m A (pre ++ (if existsb (Nat.eqb i) idxs then conv8 c else c) :: cs)).
  { destruct (existsb (Nat.eqb i) idxs); [apply rw_cells_conv8; exact H| exact H]. }
  specialize (IH (pre ++ [if existsb (Nat.eqb i) idxs then conv8 c else c]) (S i)).
  rewrite <- !app_assoc in IH. cbn [app] in IH. exact (IH H1).
Qed.
Lemma rw_cells_conv_sel0 : forall idxs m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (conv_sel idxs 0 cs).
Proof. intros idxs m A cs H. exact (rw_cells_conv_sel idxs m A cs [] 0 H). Qed.

Definition vinvx (ra : word) (q : Z) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word) (m0 : word -> option byte)
    (T : Z) (txt : list Z) (canary : word) (P1 P2 P3 FA : Z) (fmtl : list Z) (w3n : nat) (ap3w : word)
    (apz : Z) (j32 j40 : word) (mt : Z) (j64 : word) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ munch (vf_FP q P1 P2 P3) m0 m /\ wmono rsegs m0 m
  /\ (exists j16 j56 j72, rw_cells rsegs m (q + -480) (vlow (Z_to_bv 64 apz) j16 j32 j40 mt j56 j64 j72))
  /\ (exists scs, rw_cells rsegs m (q + -368) [CB 256 scs])
  /\ rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e)
  /\ stk rsegs m (q - VF_DEPTH) (q + -480)
  /\ bytes_at rsegs m T (zbytes txt) /\ ssp_cells m canary
  /\ (exists ev : word, rw_cells rsegs m ERRNOA [C4 ev])
  /\ rw_cells rsegs m (q + 320) [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w]
  /\ (exists (v1 v2 : word) (v3 : list byte), rw_cells rsegs m P1 [C4 v1] /\ rw_cells rsegs m P2 [C4 v2] /\ rw_cells rsegs m P3 [CB w3n v3])
  /\ bytes_at rsegs m FA (zbytes fmtl).

Lemma vinvx_vinv : forall ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 T txt canary P1 P2 P3 FA fmtl w3n ap3w na j32 j40 mt j64 m,
  vinvx ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 T txt canary P1 P2 P3 FA fmtl w3n ap3w (q + 320 + 8 * na) j32 j40 mt j64 m ->
  vinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 T txt canary P1 P2 P3 FA fmtl w3n ap3w na mt m.
Proof.
  intros. destruct H as (MI & MU & WM & (j16 & j56 & j72 & LOW) & REST).
  unfold vinv. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [|exact REST].
  exists j16, j32, j40, j56, j64, j72. exact LOW.
Qed.
