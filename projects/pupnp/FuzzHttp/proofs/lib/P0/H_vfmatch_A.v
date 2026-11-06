(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs F_ctype H_scanner_get_token.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition vfmatch_entry := 0x1403c%Z.
Notation VF_HEAD := 0x140b8%Z.
Notation VF_CONT := 0x14210%Z.
Notation MASK := 4294977024%Z.
Ltac sstep := step; fix_lit_store.
Ltac dex := repeat match goal with H : ex _ |- _ => destruct H as [? H] end.

Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Lemma ltb1_eqb0_mod : forall x, (-2^63 <= x < 2^63)%Z -> (x mod 18446744073709551616 <? 1)%Z = (x =? 0)%Z.
Proof.
  intros x Hx. destruct (Z.eqb_spec x 0). { subst. vm_compute. reflexivity. }
  apply Z.ltb_ge. destruct (Z.lt_ge_cases x 0).
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.
Lemma ltb1_eqb0 : forall x, (0 <= x)%Z -> (x <? 1)%Z = (x =? 0)%Z.
Proof. intros x Hx. destruct (Z.eqb_spec x 0); [subst; reflexivity|]. apply Z.ltb_ge. lia. Qed.
Lemma pos_mod : forall x, (-2^63 <= x < 2^63)%Z -> (0 <? x mod 18446744073709551616)%Z = negb (x =? 0)%Z.
Proof.
  intros x Hx. destruct (Z.eqb_spec x 0) as [E|E]. { rewrite E. vm_compute. reflexivity. }
  cbn [negb]. apply Z.ltb_lt. destruct (Z.lt_ge_cases x 0).
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.
Lemma pos_nomod : forall x, (0 <= x)%Z -> (0 <? x)%Z = negb (x =? 0)%Z.
Proof. intros x Hx. destruct (Z.eqb_spec x 0) as [E|E]; cbn [negb]. { rewrite E. reflexivity. } apply Z.ltb_lt. lia. Qed.
Lemma land_b2z : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma b2z_0 : forall c, Z.b2z c = 0%Z <-> c = false.
Proof. intros [|]; cbn; split; intros; congruence. Qed.
Lemma b2z_n0 : forall c, Z.b2z c <> 0%Z <-> c = true.
Proof. intros [|]; cbn; split; intros; congruence. Qed.
Lemma land_255_small : forall c, (0 <= c < 256)%Z -> Z.land c 255 = c.
Proof. intros c Hc. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac cond_norm K :=
  rewrite ?ltb1_eqb0_mod in K by lia; rewrite ?ltb1_eqb0 in K by lia;
  rewrite ?pos_mod in K by lia; rewrite ?pos_nomod in K by lia;
  rewrite ?land_b2z in K; first [apply b2z_0 in K | apply b2z_n0 in K | idtac];
  repeat (match type of K with context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end); cbn in K; try discriminate.

Definition sgt_qpost (ra : word) (qq lo : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S T TY MB A cur len : Z) (bs : list byte) (tyw : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r cur' : Z) (tb tl : word) (tyw' : word),
    ms' = MS (mkR ra (wz qq) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(qq - 96, qq); (S + 8, S + 16); (T, T + 16); (TY, TY + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo qq
    /\ rw_cells rsegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)]
    /\ rw_cells rsegs m' T [C8 tb; C8 tl]
    /\ rw_cells rsegs m' TY [C4 tyw']
    /\ (0 <= cur' <= len)%Z
    /\ ( (exists tlz ty, r = PARSE_OK /\ tb = wz (A + cur) /\ tl = wz tlz /\ tyw' = wz ty
             /\ 1 <= tlz /\ cur' = cur + tlz /\ cur' <= len /\ 0 <= ty <= 5
             /\ ((ty = TT_IDENTIFIER \/ ty = TT_WHITESPACE) -> cur' < len)
             /\ (ty = TT_CRLF -> exists b, nth_error bs (Z.to_nat cur) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10))
             /\ (ty = TT_CRLF -> tlz <= 2))
       \/ ((r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE) /\ cur' = cur /\ tyw' = tyw) )%Z.

Lemma sgt_call : forall (qq lo S T TY MB A cur len cap : Z) (bs : list byte) (tw1 tw2 tyw : word)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)] ->
  rw_cells rsegs m MB (mbuf_cells A len cap) ->
  bytes_at rsegs m A bs -> (Z.of_nat (length bs) >= len)%Z -> (0 <= cur <= len)%Z -> (len <= cap)%Z -> (A + cap + 1 < 2^63)%Z ->
  rw_cells rsegs m T [C8 tw1; C8 tw2] ->
  rw_cells rsegs m TY [C4 tyw] ->
  stk rsegs m lo qq -> (0 <= lo)%Z -> (lo + 96 <= qq)%Z -> (256 <= qq < 2^63)%Z ->
  (A + Z.of_nat (length bs) <= lo)%Z -> (0 < A \/ (A = 0 /\ len = 0))%Z ->
  (qq <= T)%Z -> (qq <= TY)%Z -> (T + 16 <= TY \/ TY + 4 <= T)%Z ->
  (T + 16 <= MB)%Z -> (TY + 4 <= MB)%Z -> (MB + 32 <= S)%Z -> (S + 24 < 2^63)%Z ->
  mem_inv rsegs m -> a0 = wz S -> a1 = wz T -> a2 = wz TY ->
  evt rsegs (sgt_qpost ra qq lo gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S T TY MB A cur len bs tyw m)
      (MS (mkR ra (wz qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz sgt_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros SC MBC BUF LBS CUR CAP AHI TC TYC ST LO0 LO96 QQ BLO ANZ LT LTY TTY TMB TYMB MBS SHI MI -> -> ->.
  assert (E : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  destruct (stk_split rsegs _ _ (qq - 96)%Z _ ST ltac:(lia)) as [STlo SThi].
  eapply evt_mono.
  { eapply (scanner_get_token_spec S T TY MB A cur len cap bs tw1 tw2 tyw); rewrite ?E; eauto; try lia. }
  intros ms' P. unfold sgt_post in P. rewrite !E in P. unfold sgt_qpost.
  destruct P as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & r & cur' & tb & tl & tyw' & -> & MU & WM & MI' & ST' & SC' & TC' & TYC' & RES).
  pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m', r, cur', tb, tl, tyw'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  split. { eapply stk_merge; [| exact ST'| lia]. eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM|]. cbn [disjoint_from]. lia. }
  split; [exact SC'|]. split; [exact TC'|]. split; [exact TYC'|].
  split. { destruct RES as [(tlz & ty & R)|R]; lia. }
  exact RES.
Qed.

Notation VJT := 0x10710%Z.
Definition vjt356 : list byte := map (Z_to_bv 8)
  [240; 57; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 240; 57; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 92; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 40; 60; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 132; 59; 0; 0; 0; 59; 0; 0; 152; 59; 0; 0; 140; 60; 0; 0; 0; 59; 0; 0; 148; 60; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 136; 61; 0; 0; 28; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 132; 60; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 124; 60; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 44; 59; 0; 0; 0; 59; 0; 0; 32; 61; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 0; 59; 0; 0; 84; 61; 0; 0; 28; 59; 0; 0]%Z.
Lemma vjt_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m VJT vjt356.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m VJT vjt356 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition vjt_off (c2 : Z) : Z :=
  if c2 =? 99 then 15752 else if c2 =? 115 then 15648 else if c2 =? 120 then 15132 else if c2 =? 83 then 15500
  else if c2 =? 76 then 15400 else if c2 =? 105 then 15492 else if c2 =? 119 then 15700 else if c2 =? 82 then 15256 else 0.
Definition vjt_char (c2 : Z) : bool := ((c2 =? 99) || (c2 =? 115) || (c2 =? 120) || (c2 =? 83) || (c2 =? 76) || (c2 =? 105) || (c2 =? 119) || (c2 =? 82))%bool.
Lemma vjt_read : forall m c2, mem_inv rsegs m -> vjt_char c2 = true ->
  ov_read_bytes rsegs m (wa (VJT + 4 * (c2 - 32))) 4 = Some (le4 (Z_to_bv 64 (vjt_off c2))).
Proof.
  intros m c2 MI Hc. pose proof (vjt_bytes m MI) as B.
  assert (CASES : c2 = 99 \/ c2 = 115 \/ c2 = 120 \/ c2 = 83 \/ c2 = 76 \/ c2 = 105 \/ c2 = 119 \/ c2 = 82).
  { unfold vjt_char in Hc. repeat (apply orb_prop in Hc; destruct Hc as [Hc|Hc]); try (apply Z.eqb_eq in Hc; lia). }
  destruct CASES as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
    (rewrite (bytes_at_read rsegs m VJT vjt356 _ 4 B) by (cbn; lia)); f_equal; apply bytes_eqb_eq; vm_compute; reflexivity.
Qed.

Section DEFS.
Context {HCEIL : HasCeiling}.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Notation qq := (q + -208)%Z.
  Definition SCc (m : mem) (cur : Z) := rw_cells rsegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)].
  Definition MBc (m : mem) := rw_cells rsegs m MB (mbuf_cells A len cap).
  Definition BUFc (m : mem) := bytes_at rsegs m A bs.

  Definition F0 (m : mem) (w8 : word) := exists j0 j32, rw_cells rsegs m qq [CB 8 j0; C8 w8; C8 (wz cur0); C8 (wz MASK); CB 4 j32].
  Definition F36 (m : mem) (ty : word) := rw_cells rsegs m (q + -172) [C4 ty].
  Definition F40 (m : mem) (tb tl : word) := rw_cells rsegs m (q + -168) [C8 tb; C8 tl].
  Definition F56 (m : mem) := exists ua ub, rw_cells rsegs m (q + -152) [C8 ua; C8 ub].
  Definition F72 (m : mem) (ty : word) := rw_cells rsegs m (q + -136) [C4 ty].
  Definition F76 (m : mem) := exists j, rw_cells rsegs m (q + -132) [CB 8 j].
  Definition F84 (m : mem) (ty : word) := rw_cells rsegs m (q + -124) [C4 ty].
  Definition F88 (m : mem) (tb tl : word) := rw_cells rsegs m (q + -120) [C8 tb; C8 tl].

  Definition FX (m : mem) := (exists w8, F0 m w8) /\ (exists ty, F36 m ty) /\ (exists tb tl, F40 m tb tl) /\ F56 m
                             /\ (exists ty, F72 m ty) /\ F76 m /\ (exists ty, F84 m ty) /\ (exists tb tl, F88 m tb tl).

  Definition contst (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (r fp' G' cs' : Z)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G') (wz r) x11 x12 x13 x14 x15 x16 x17 x18 x19 (wz cs')
            (wz 1) (wz 9) (wz 4) (wz 32) (wz 2) (wz 37) (wz fp') x28 x29 x30 x31)
       F (wz VF_CONT) fc None m (seg_rom rsegs).

  Notation W0 := [(q - 304, q - 104); (S + 8, S + 16)]%Z.

  Definition exitst (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (r : Z)
      (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) x9 x10 (wz r) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (wz 0x1465c) fc None m (seg_rom rsegs).

  Definition dpost (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fp' G' cs' : Z) (W : list ivl)
      (X : mem -> Z -> Z -> Prop) (XE : mem -> Prop) (m : mem) : machine_state -> Prop :=
    fun ms' =>
      (exists (r cur' : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m',
        ms' = contst gp tp F fc r fp' G' cs' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m'
        /\ munch W m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo qq
        /\ SCc m' cur' /\ MBc m' /\ BUFc m' /\ FX m'
        /\ (0 <= cur' <= len)%Z /\ (0 <= r <= 5)%Z
        /\ X m' r cur')
      \/ (exists (r cur' : Z) x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
        ms' = exitst gp tp F fc r x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m'
        /\ munch W m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo qq
        /\ SCc m' cur' /\ MBc m' /\ BUFc m' /\ FX m'
        /\ (0 <= cur' <= len)%Z /\ (0 <= r <= 5)%Z
        /\ r <> 4 /\ XE m').

  Definition headst (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fp c G cs : Z)
      (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) x10 (wz fp) (wz c) x13 x14 x15 x16 x17 x18 x19 (wz cs)
            (wz 1) (wz 9) (wz 4) (wz 32) (wz 2) (wz 37) x27 x28 x29 x30 x31)
       F (wz VF_HEAD) fc None m (seg_rom rsegs).

  Definition linv (W : list ivl) (m0 m : mem) (cur : Z) (w8 : word) : Prop :=
    SCc m cur /\ MBc m /\ BUFc m /\ F0 m w8 /\ (exists ty, F36 m ty) /\ (exists tb tl, F40 m tb tl) /\ F56 m
    /\ (exists ty, F72 m ty) /\ F76 m /\ (exists ty, F84 m ty) /\ (exists tb tl, F88 m tb tl)
    /\ stk rsegs m lo qq /\ mem_inv rsegs m /\ munch W m0 m /\ wmono rsegs m0 m.
End DEFS.

Lemma lxor_b2z_5 : forall b, Z.lxor (Z.b2z b) 5 = (if b then 4 else 5)%Z.
Proof. intros [|]; reflexivity. Qed.

Ltac dfinish r c :=
  let pc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => pc end in
  apply evt_done; unfold dpost, contst, exitst, SCc, MBc, BUFc, mbuf_cells, MEMBUF_DEF_SIZE_INC, FX, F0, F36, F40, F56, F72, F76, F84, F88;
  unfold PARSE_OK, TT_IDENTIFIER, TT_WHITESPACE, TT_CRLF in *;
  lazymatch pc with 83548%Z => right | _ => left end;
  exists r, c; repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- ex _ => repeat (lazymatch goal with |- ex _ => eexists end); eassumption | _ => idtac end; try assumption; try exact I; try (unfold PARSE_OK; lia).

Ltac sgtcall_ qq lo S T TY MB A cur len cap bs :=
  try rename CUR' into CUR'';
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  eapply evt_cut;
  [ eapply (sgt_call qq lo S T TY MB A cur len cap bs); try eassumption; try reflexivity; unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; try eassumption; lia
  | post_call rsegs m;
    try rename MI0 into MI; rename PC into ST; rename PC0 into SC; rename PC1 into TC; rename PC2 into TYC; rename PC3 into CUR'; rename POST into RES ]
  end.

Ltac unf := unfold headst; unfold SCc, MBc, mbuf_cells, MEMBUF_DEF_SIZE_INC, BUFc, F0, F36, F40, F56, F72, F76, F84, F88 in *; dex.
Ltac name_r := try rename rr into rr'; lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end.

Ltac open_linv H := unfold linv in H;
  destruct H as (SC & MBC & BUF & FR0 & FR36 & FR40 & FR56 & FR72 & FR76 & FR84 & FR88 & ST & MI & MU & WM);
  unfold SCc, MBc, mbuf_cells, MEMBUF_DEF_SIZE_INC, BUFc, F0, F36, F40, F56, F72, F76, F84, F88 in *; dex.
Ltac close_linv := unfold linv, SCc, MBc, mbuf_cells, MEMBUF_DEF_SIZE_INC, BUFc, F0, F36, F40, F56, F72, F76, F84, F88;
  repeat match goal with |- _ /\ _ => split end;
  repeat match goal with |- ex _ => repeat (lazymatch goal with |- ex _ => eexists end); eassumption end; try eassumption.

Definition vf_ok (q lo S MB A len cap cur0 : Z) (bs : list byte) : Prop :=
  (512 <= lo /\ lo + 304 <= q /\ q + 64 <= MB /\ MB + 32 <= S /\ S + 24 < 2^63
   /\ A + Z.of_nat (length bs) <= lo /\ (0 < A \/ (A = 0 /\ len = 0)) /\ Z.of_nat (length bs) >= len
   /\ 0 <= cur0 <= len /\ len <= cap /\ A + cap + 1 < 2^63)%Z.
Ltac vok V := destruct V as (LO0 & LOQ & QMB & MBS & SHI & BLO & ANZ & LBS & CUR0 & CAP & AHI).

Section VF.
Context {HCEIL : HasCeiling}.

  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation W0 := [(q - 304, q - 104); (S + 8, S + 16)]%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation linv := (linv q lo S MB A len cap cur0 bs).
  Notation headst := (headst q S). Notation contst := (contst q S). Notation exitst := (exitst q S).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q cur0).
  Notation F0 := (F0 q cur0). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).
  Ltac sgtcall T TY cur := sgtcall_ (q + -208)%Z lo S T TY MB A cur len cap bs.

  #[using="lo MB A len cap cur0 bs VOK"] Lemma pct_dispatch : forall (Q : machine_state -> Prop) (fp c2 G cs : Z) (b2 : byte) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m,
    mem_inv rsegs m -> vjt_char c2 = true -> (0 <= fp /\ fp + 2 < 2^63)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = c2 ->
    evt rsegs Q (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) (wz 4) (wz (vjt_off c2 + VJT)) (wz VJT) x13 x14 x15 x16 x17 (wz c2) (wz (q + -152)) (wz cs)
                        (wz 1) (wz 9) (wz 4) (wz 32) (wz 2) (wz 37) (wz (fp + 2)) x28 x29 x30 x31)
                   F (wz (vjt_off c2 + VJT)) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (headst gp tp F fc fp 37 G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros MI VC FP RD Hb2 H. unfold headst.
    assert (CR : (32 <= c2 <= 120)%Z).
    { unfold vjt_char in VC. repeat (apply orb_prop in VC; destruct VC as [VC|VC]); try (apply Z.eqb_eq in VC; lia). }
    pose proof (vjt_read m c2 MI VC) as TR.
    zstep. zstep. lit_branch. zstep. lit_branch. zstep. lit_branch.
    zstep. cbn beta. rewrite Hb2. zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. lia. }
    replace (wa (VJT + 4 * (c2 - 32))) with (Z_to_bv 64 (Z.shiftl (c2 + -32) 2 + VJT))%Z in TR
      by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (OFF : (0 <= vjt_off c2 < 2^16)%Z /\ (vjt_off c2 + VJT) mod 2 = 0) by (unfold vjt_off; repeat (destruct (Z.eqb _ _)); cbn; lia).
    zstep. zstep. zstep. zstep. zstep. rewrite sx32_lit by lia. zstep. zstep. zstep.
    rewrite ret_pc_even by lia. exact H.
  Qed.

  #[using="VOK"] Lemma dir_tab : forall (fp G cs cur : Z) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur + 1 <= cur')%Z (fun _ => False) m)
        (headst gp tp F fc fp 9 G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS.
    unfold headst. unfold SCc in SC. unfold MBc, mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC. unfold BUFc in BUF.
    unfold F0 in FR0. unfold F36 in FR36. unfold F40 in FR40. unfold F56 in FR56. unfold F72 in FR72. unfold F76 in FR76. unfold F84 in FR84. unfold F88 in FR88. dex.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. lit_branch.
    zstep. zstep. zstep. zstep.
    sgtcall (q + -168) (q + -172) cur.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    -   zstep. rewrite (sx32_lit ty) by lia. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + cond_norm K1. all: dfinish rr (cur + tlz)%Z.
      + zstep. zstep. dfinish 5 (cur + tlz)%Z.
    - pose proof (word_lt64 ty36) as TYB.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + dfinish rr cur.
      + zstep. zstep. dfinish 5 cur.
  Qed.

  #[using="VOK"] Lemma dir_c : forall (fp G cs cur : Z) (b2 : byte) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 99 ->
    evt rsegs (dpost gp tp F fc (fp + 2) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur + 1 <= cur')%Z (fun _ => False) m)
        (headst gp tp F fc fp 37 G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2.
    eapply (pct_dispatch _ fp 99); [exact MI| reflexivity| lia| exact RD| exact Hb2|]. cbn [vjt_off Z.eqb Pos.eqb Z.add]. unf.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. zstep. zstep.
    sgtcall (q + -168) (q + -172) cur. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. rewrite (sx32_lit ty) by lia. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + cond_norm K1. all: dfinish rr (cur + tlz)%Z.
      + zstep. zstep. zstep. dfinish 5 (cur + tlz)%Z.
    - pose proof (word_lt64 ty36) as TYB.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + dfinish rr cur.
      + zstep. zstep. zstep. dfinish 5 cur.
  Qed.

  #[using="VOK"] Lemma dir_w : forall (fp G cs cur : Z) (b2 : byte) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 119 ->
    evt rsegs (dpost gp tp F fc (fp + 2) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur <= cur')%Z (fun _ => False) m)
        (headst gp tp F fc fp 37 G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2.
    eapply (pct_dispatch _ fp 119); [exact MI| reflexivity| lia| exact RD| exact Hb2|]. cbn [vjt_off Z.eqb Pos.eqb Z.add]. unf.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. zstep. zstep. zstep.
    sgtcall (q + -168) (q + -172) cur. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. rewrite (sx32_lit ty) by lia. zstep. if_cases K1; zify_cond K1.
      + dfinish rr (cur + tlz)%Z.
      + zstep. zstep. zstep. sstep. zstep. zstep.
        replace (cur + tlz - tlz)%Z with cur in SC by lia. dfinish 4 cur.
    - zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
      dfinish rr cur.
  Qed.

  #[using="VOK"] Lemma dir_i : forall (fp G cs cur : Z) (b2 : byte) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 105 ->
    evt rsegs (dpost gp tp F fc (fp + 2) G 0 W0 (fun m' r cur' => r = PARSE_OK /\ cur' = cur)%Z (fun _ => False) m)
        (headst gp tp F fc fp 37 G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2.
    eapply (pct_dispatch _ fp 105); [exact MI| reflexivity| lia| exact RD| exact Hb2|]. cbn [vjt_off Z.eqb Pos.eqb Z.add]. unf.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. dfinish 4 cur.
  Qed.

  #[using="VOK"] Lemma dir_s : forall (fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 115 ->
    rw_cells rsegs m G [C8 (wz P)] -> rw_cells rsegs m P [C8 pw1; C8 pw2] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z
                 (fun m' r cur' => exists pa pb, rw_cells rsegs m' P [C8 pa; C8 pb]
                     /\ (r = PARSE_OK -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len))%Z (fun _ => False) m)
        (headst gp tp F fc fp 37 G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2 GC PC PL.
    eapply (pct_dispatch _ fp 115); [exact MI| reflexivity| lia| exact RD| exact Hb2|]. cbn [vjt_off Z.eqb Pos.eqb Z.add]. unf.
    pose proof (munch_refl [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. zstep. zstep. zstep.
    sgtcall P (q + -172) cur. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. rewrite (sx32_lit ty) by lia. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + cond_norm K1. all: zstep; zstep; dfinish rr (cur + tlz)%Z.
        all: do 2 eexists; split; [exact TC|]; intros _; exists tlz; repeat split; try reflexivity; lia.
      + zstep. zstep. zstep. dfinish 5 (cur + tlz)%Z. do 2 eexists; split; [exact TC|]. intros; exfalso; lia.
    - pose proof (word_lt64 ty36) as TYB.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + zstep. zstep. dfinish rr cur. do 2 eexists; split; [exact TC|]. intros; exfalso; lia.
      + zstep. zstep. zstep. dfinish 5 cur. do 2 eexists; split; [exact TC|]. intros; exfalso; lia.
  Qed.

  #[using="q lo S MB A cap cur0 VOK"] Lemma nth_bs : forall i, (0 <= i < len)%Z -> exists b, nth_error bs (Z.to_nat i) = Some b.
  Proof.
    vok VOK.
    intros i Hi. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.
  #[using="Type"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

  #[using="VOK"] Lemma dir_lit : forall (fp c G cs cur : Z) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    (0 < c < 256)%Z -> c <> 9 -> c <> 32 -> c <> 37 ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => cur' = cur + 1)%Z (fun _ => True) m)
        (headst gp tp F fc fp c G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS CR N9 N32 N37. unf.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. zstep. if_cases K; zify_cond K. { exfalso; lia. }
    zstep. if_cases K'; zify_cond K'. { exfalso; lia. }
    zstep. if_cases K''; zify_cond K''. 2:{ exfalso; lia. }
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
    {   zstep. dfinish 1 cur. }
    destruct (nth_bs cur ltac:(lia)) as [b0 Hb0]. pose proof (byte_range b0) as BR0.
    zstep. zstep. sstep. zstep.
    pose proof (u8ro_read rsegs _ A bs cur b0 (Z_to_bv 64 (A + cur)) BUF Hb0 ltac:(lia) eq_refl) as RD0.
    zstep. zstep. if_cases K1; zify_cond K1.
    -
      zstep. rewrite land_255_small by lia. zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
      zstep. zstep. zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
      zstep. zstep. zstep.
      match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => rewrite (lxor_b2z_5 bb); destruct bb end.
      * dfinish 4 (cur + 1)%Z. * dfinish 5 (cur + 1)%Z.
    - zstep. zstep. zstep. zstep.
      match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => rewrite (lxor_b2z_5 bb); destruct bb end.
      * dfinish 4 (cur + 1)%Z. * dfinish 5 (cur + 1)%Z.
  Qed.

  #[using="VOK"] Lemma sp_loop : forall (k : nat) (fp G cs cur curi : Z) gp tp (F : bvmap 5 word) fc (w8 : word) m0
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m,
    (len - curi < Z.of_nat k)%Z -> (cur0 <= cur <= curi)%Z -> (curi <= len)%Z ->
    linv W0 m0 m curi w8 -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur <= cur')%Z (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (wz cs)
               (wz 1) (wz 9) (wz 4) (wz 32) (wz 2) (wz 37) (wz (fp + 1)) x28 x29 x30 x31)
          F (wz 0x1413c) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    induction k as [|k IH]; intros until m; intros HK HC HL LI FP GR CS; [lia|].
    open_linv LI.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. zstep. zstep. zstep. zstep.
    sgtcall (q + -120) (q + -136) curi. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.

    assert (TAIL : forall (r : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 m',
      linv W0 m0 m' curi w8 -> (r = 1 \/ r = 3 \/ r = 4)%Z ->
      evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur <= cur')%Z (fun _ => False) m0)
        (MS (mkR y1 (wz qq) gp tp y5 y6 y7 (wz S) (wz G) (wz r) y11 y12 y13 y14 y15 y16 y17 y18 y19 (wz cs)
                 (wz 1) (wz 9) (wz 4) (wz 32) (wz 2) (wz 37) (wz (fp + 1)) y28 y29 y30 y31)
            F (wz 0x14178) fc None m' (seg_rom rsegs))).
    { intros until m'. intros LI' HR. clear - LO0 LOQ QMB MBS SHI BLO ANZ LBS CUR0 CAP AHI HC HL FP GR CS LI' HR. open_linv LI'.
      pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
      zstep. if_cases K0; zify_cond K0.
      - dfinish r curi.
      - zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
        zstep. zstep. dfinish 1 curi. }
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. rewrite (sx32_lit ty) by lia. zstep. if_cases K1; zify_cond K1.
      +   zstep. zstep. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
        zstep. if_cases K3; zify_cond K3.
        *   sstep. apply (TAIL 4); [| lia]. close_linv.
        *   eapply (IH fp G cs cur (curi + tlz)%Z); try lia. close_linv.
      +   zstep. zstep. zstep. zstep.
        sgtcall (q + -120) (q + -136) (curi + tlz)%Z. name_r.
        unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
        destruct RES as [(tlz2 & ty2 & HR2 & -> & -> & -> & TL2 & -> & _ & TY52 & STRICT2 & CRB2 & CRL2)|(HR2 & -> & ->)].
        * zstep. rewrite (sx32_lit ty2) by lia. zstep. if_cases K4; zify_cond K4. 2:{ exfalso; lia. }
          zstep. if_cases K3; zify_cond K3.
          -- sstep. apply (TAIL rr); [| lia]. close_linv.
          -- eapply (IH fp G cs cur (curi + tlz + tlz2)%Z); try lia. close_linv.
        * zstep. rewrite (sx32_lit ty) by lia. zstep. if_cases K4; zify_cond K4. { exfalso; lia. }
          sstep. apply (TAIL rr); [| lia]. close_linv.
    - zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
      apply (TAIL rr); [| lia]. close_linv.
  Qed.

  #[using="VOK"] Lemma dir_sp : forall (fp G cs cur : Z) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 1) G cs W0 (fun m' r cur' => r = PARSE_OK -> cur <= cur')%Z (fun _ => False) m)
        (headst gp tp F fc fp 32 G cs x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS. unfold headst.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. lit_branch. zstep. lit_branch.
    eapply (sp_loop (Datatypes.S (Z.to_nat (len - cur))) fp G cs cur cur); try lia.
    unfold F0, F36, F40, F56, F72, F76, F84, F88 in *. close_linv.
  Qed.
End VF.
