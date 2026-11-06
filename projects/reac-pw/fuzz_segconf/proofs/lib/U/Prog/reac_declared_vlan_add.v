(** reac_declared_vlan_add (UBSan build, 0x16530, 112-byte frame): proof of [reac_declared_vlan_add_contract]
    (U/Prog/reac_declared_vlan_add_c.v) from the contracts of its callees strcmp (U/Prog/strcmp_c.v), memset
    (U/Prog/memset_c.v) and strncpy (U/Prog/strncpy_c.v). Written new; the plain walk
    is lib/Prog/reac_declared_vlan_add.v, and the pure facts both use are lib/Prog/reac_declared_vlan_add_facts.v.

    Code (the UBSan binary, image 1696d6c34ffd):
      0x16530-0x16564  frame of 112: ra s0-s11 at sp+104 .. sp+8 (sp+0 .. sp+8 not written)
      0x16568 s4 = -1; beqz a0 / a2 / a3 -> EPI; s0 = n; s3 = parent; s2 = tab; 0x16588 n & 3 -> TRAP; s1 = vid;
              s5 = max; 0x16594 lw s7,0(s0) (s7 = *n = length t); 0x16598 blez s7 -> 0x165e8
      0x1659c s8 = 0; s9 = ~tab; s10 = tab & 1; s11 = (s7 > 0 ? s7 : 0) = *n; s6 = tab
      LOOP 0x165b8 (s6 = &tab[i], s8 = 18 i, s11 = *n - i): bltu s9,s8 -> TRAP; bnez s10 -> TRAP; lhu a0,16(s6);
           bne a0,s1 -> NEXT; strcmp(s6, parent); 0x165d4 beqz a0 -> DUP.
           NEXT 0x165d8: s11 -= 1; s6 += 18; s8 += 18; bnez s11 -> LOOP
      0x165e8 bge s7,s5 -> EPI (a0 = -1)
      0x165ec a0 = tab + 18 *n: beqz -> TRAP, (a0 <u tab) xor (s7 < 0) = 0 -> TRAP (pointer overflow)
      0x16610 memset(tab + 18 *n, 0, 18) (`jal` 0x16624); a0 = tab + 18 *n: the same two checks and a0 & 1 -> TRAP;
              strncpy(a0, parent, 15) (`jal` 0x1665c); a0 = tab + 18 *n: the same three checks; `sh` vid at a0 + 16;
              a0 = *n + 1 (`addiw`); blt a0,*n -> TRAP (signed overflow); `sw`; s4 = 1; j EPI.  DUP 0x166ac: s4 = 0
      EPI 0x166b0: a0 = s4; restore ra s0-s11; ret.  TRAP 0x166f0: unimp.
    The traps are not reached (the contract's comment): n mod 4 = 0; tab + 18 i <= tab + 18 *n <= 2^64 (rtab_at's
    bytes_at bound and the free entries' rw_cells bound); tab mod 16 = 0, so tab and tab + 18 *n are even; tab <> 0;
    0 <= *n < max < 2^31. Shape as the plain walk: [epi], [keep_exit], [uapp_tail] (the stores), [uapp_sn]
    (strncpy), [uapp_ms] (memset), [after], [sloop], [body]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts
  seg_tok_bridge reac_declared_vlan_add_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import check_declared strcmp_c memset_c
  stpncpy_c strncpy_c reac_declared_vlan_add_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require reac_segconf_find.
Import ListNotations.
Open Scope Z_scope.

Ltac ul := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.
Ltac weq := first [ reflexivity | f_equal; ul; lia | apply bv_eq; ul; lia ].
Ltac ulh H := repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] =>
  rewrite (unsigned_lit z) in H by lia end.
Ltac dj := cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia.
Ltac djh H := lazymatch type of H with ?A -> _ => let P := fresh "P" in assert (P : A) by dj; specialize (H P); clear P end.
(** A branch to the trap (or an exit) that the facts in the context say is not taken. *)
Ltac ntk := let K := fresh "K" in
  if_cases K; [exfalso; zify_cond K; first [lia | Z.div_mod_to_equations; lia] | clear K; cbv iota].

(** ** The values the UBSan checks compute *)
Lemma au_land3 : forall x, 0 <= x < 2 ^ 64 -> x mod 4 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 3 = 0.
Proof.
  intros x Hx H. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H.
Qed.

Lemma au_land1 : forall x, 0 <= x < 2 ^ 64 -> x mod 2 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 1 = 0.
Proof.
  intros x Hx H. rewrite unsigned_lit by lia.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. exact H.
Qed.

Lemma au_sltu_ge : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> y <= x ->
  v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 0.
Proof.
  intros x y Hx Hy H. rewrite v_sltu_b2z, !unsigned_lit by lia.
  destruct (Z.ltb_spec x y); [lia | reflexivity].
Qed.

Lemma au_slti0 : forall x, 0 <= x < 2 ^ 63 -> v_slti (Z_to_bv 64 x) 0 = Z_to_bv 64 0.
Proof.
  intros x Hx. rewrite v_slti_b2z, unsigned_lit by lia. rewrite zb_lxor_sign by lia. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (x + 2 ^ 63) (0 + 2 ^ 63)); [lia | reflexivity].
Qed.

Section Add.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (Sp lo tab max n par vid : Z) (t : list (list Z * Z)) (p : list Z)
  (bt free pb psl : list byte).
Hypothesis HSC : strcmp_contract.
Hypothesis HMS : memset_contract.
Hypothesis HSN : strncpy_contract.
Hypothesis HBT : bytes_at rsegs m0 tab bt.
Hypothesis HET : rtab_enc t bt.
Hypothesis Lbt : length bt = (18 * length t)%nat.
Hypothesis HLm : Z.of_nat (length t) <= max < 2 ^ 31.
Hypothesis HFR : rw_cells rsegs m0 (tab + 18 * Z.of_nat (length t))
                   [CB (Z.to_nat (18 * (max - Z.of_nat (length t)))) free].
Hypothesis Htab : 0 < tab < 2 ^ 64.
Hypothesis Htab16 : tab mod 16 = 0.
Hypothesis HAT : apart tab (18 * (max + 1)) lo Sp.
Hypothesis HN : rw_cells rsegs m0 n [C4 (Z_to_bv 64 (Z.of_nat (length t)))].
Hypothesis Hn : 0 < n < 2 ^ 64.
Hypothesis Hn4 : n mod 4 = 0.
Hypothesis HnA : apart n 4 lo Sp.
Hypothesis HnT : apart n 4 tab (tab + 18 * (max + 1)).
Hypothesis HPB : bytes_at rsegs m0 par (pb ++ Z_to_bv 8 0 :: psl).
Hypothesis HPZ : zs pb = p.
Hypothesis HPN0 : ~ In 0 p.
Hypothesis HPN : ~ In (Z_to_bv 8 0) pb.
Hypothesis HPL : length pb = length p.
Hypothesis HPS : (- (par + Z.of_nat (length pb) + 1)) mod 8 <= Z.of_nat (length psl).
Hypothesis HPS8 : Z.of_nat (length psl) < 8.
Hypothesis Hpar : 0 < par < 2 ^ 64.
Hypothesis HPA : apart par (Z.of_nat (length p) + 8) lo Sp.
Hypothesis HPT : apart par (Z.of_nat (length p) + 8) tab (tab + 18 * (max + 1)).
Hypothesis HV : 0 <= vid < 65536.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 144 <= Sp.
Hypothesis HS : Sp < 2 ^ 64.

Local Abbreviation VA := (vlan_add t max p vid).
Local Abbreviation Post :=
  (ret_post rsegs ra (Z_to_bv 64 Sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fst VA) m0
     (vtab_W ADD_STACK Sp tab n t (snd VA)) lo
     (fun m' => rtab_at rsegs m' tab (snd VA) /\
                rw_cells rsegs m' n [C4 (Z_to_bv 64 (Z.of_nat (length (snd VA))))])).
(** What the append path may write: the frames, tab[*n], *n. *)
Local Abbreviation Wapp :=
  [(Sp - 144, Sp); (tab + 18 * Z.of_nat (length t), tab + 18 * Z.of_nat (length t) + 18); (n, n + 4)].

(** The frame between the prologue and the epilogue (sp+0 .. sp+8 not written); W is what the walk may have
    written since the entry. *)
Definition frm (W : list ivl) (m : word -> option byte) : Prop :=
  (exists j0, rw_cells rsegs m (Sp + -112)
                [CB 8 j0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0;
                 C8 ra]) /\
  stk rsegs m lo (Sp + -112) /\ munch W m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

(** ** The entry's objects after the prologue (only the frame written) *)
Lemma frm_bt : forall m, frm [(Sp - 112, Sp)] m -> bytes_at rsegs m tab bt.
Proof.
  intros m (_ & _ & MU & _ & _). pose proof HAT as A. unfold apart in A.
  eapply bytes_at_transport; [exact HBT | exact MU |]. rewrite Lbt. dj.
Qed.

Lemma frm_n : forall m, frm [(Sp - 112, Sp)] m -> rw_cells rsegs m n [C4 (Z_to_bv 64 (Z.of_nat (length t)))].
Proof.
  intros m (_ & _ & MU & WM & _). pose proof HnA as A. unfold apart in A.
  eapply rw_cells_transport; [exact HN | exact MU | exact WM |]. dj.
Qed.

Lemma frm_par : forall m, frm [(Sp - 112, Sp)] m -> bytes_at rsegs m par (pb ++ Z_to_bv 8 0 :: psl).
Proof.
  intros m (_ & _ & MU & _ & _). pose proof HPA as A. unfold apart in A.
  eapply bytes_at_transport; [exact HPB | exact MU |]. rewrite length_app. cbn [length]. dj.
Qed.

Lemma frm_parz : forall m, frm [(Sp - 112, Sp)] m -> bytes_at rsegs m par (pb ++ [Z_to_bv 8 0]).
Proof.
  intros m FRM. pose proof (frm_par m FRM) as H.
  replace (pb ++ Z_to_bv 8 0 :: psl) with ((pb ++ [Z_to_bv 8 0]) ++ psl) in H
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma frm_free : forall m, frm [(Sp - 112, Sp)] m ->
  rw_cells rsegs m (tab + 18 * Z.of_nat (length t)) [CB (Z.to_nat (18 * (max - Z.of_nat (length t)))) free].
Proof.
  intros m (_ & _ & MU & WM & _). pose proof HAT as A. unfold apart in A.
  eapply rw_cells_transport; [exact HFR | exact MU | exact WM |]. dj.
Qed.

(** The footprints the contract names. *)
Lemma vtab_W_keep : vtab_W ADD_STACK Sp tab n t t =
  [(Sp - 144, Sp); (tab + 18 * Z.of_nat (length t), tab + 18 * Z.of_nat (length t))].
Proof.
  unfold vtab_W, ADD_STACK, RVLAN_SIZE. rewrite Nat.ltb_irrefl, app_nil_r.
  replace (Sp - (112 + 32)) with (Sp - 144) by lia. reflexivity.
Qed.

Lemma vtab_W_app : forall x, vtab_W ADD_STACK Sp tab n t (t ++ [x]) = Wapp.
Proof.
  intros x. unfold vtab_W, ADD_STACK, RVLAN_SIZE. rewrite length_app. cbn [length].
  replace (length t <? length t + 1)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  cbn [app]. replace (Sp - (112 + 32)) with (Sp - 144) by lia.
  replace (tab + 18 * Z.of_nat (length t + 1)) with (tab + 18 * Z.of_nat (length t) + 18) by lia.
  reflexivity.
Qed.

Lemma frm_keep : forall m, frm [(Sp - 112, Sp)] m -> frm (vtab_W ADD_STACK Sp tab n t t) m.
Proof.
  intros m (FR & ST & MU & WM & MI). refine (conj FR (conj ST (conj _ (conj WM MI)))).
  rewrite vtab_W_keep. eapply munch_weaken; [|exact MU].
  unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [lia | exact I].
Qed.

(** ** The exit 0x166b0: a0 = s4, restore ra and s0-s11, return. *)
Lemma epi : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
                      x30 x31 w20 : word),
  w20 = Z_to_bv 64 (fst VA) ->
  frm (vtab_W ADD_STACK Sp tab n t (snd VA)) m ->
  rtab_at rsegs m tab (snd VA) ->
  rw_cells rsegs m n [C4 (Z_to_bv 64 (Z.of_nat (length (snd VA))))] ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 w20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x166b0) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 w20
    E20 ((j0 & FR) & ST & MU & WM & MI) HQ1 HQ2.
  do 16 step.
  apply evt_done. unfold ret_post.
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m.
  split; [subst w20; unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [|split; [exact HQ1 | exact HQ2]].
  pose proof (stk_release rsegs m lo (Sp + -112) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  rewrite unsigned_lit by lia. replace (Sp + -112 + Z.of_nat 112) with Sp in R by lia. exact R.
Qed.

(** The exit with the table unchanged (a duplicate: 0; full: -1). *)
Lemma keep_exit : forall r m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
                             x28 x29 x30 x31 w20 : word),
  vlan_add t max p vid = (r, t) -> w20 = Z_to_bv 64 r -> frm [(Sp - 112, Sp)] m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 w20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x166b0) fc None m (seg_rom rsegs)).
Proof.
  intros r m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w20 EVA E20 FRM.
  eapply epi; rewrite ?EVA; cbn [fst snd].
  - exact E20.
  - exact (frm_keep m FRM).
  - exists bt. split; [exact (frm_bt m FRM) | exact HET].
  - exact (frm_n m FRM).
Qed.

(** ** The append path *)
(** 0x16690, after strncpy and the checks, a0 = &tab[*n]: `sh` vid at +16, a0 = *n + 1 (`addiw`; blt -> TRAP not
    taken), `sw`, s4 = 1, j EPI. *)
Lemma uapp_tail : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w10 x22 x24 x25 x26 x27 : word)
                         (s15 : list byte),
  Z.of_nat (length t) < max -> existsb (vmatch vid p) t = false ->
  w10 = Z_to_bv 64 (tab + 18 * Z.of_nat (length t)) -> s15 = stpn_result pb 15 ->
  frm Wapp m ->
  bytes_at rsegs m (tab + 18 * Z.of_nat (length t)) s15 ->
  rw_cells rsegs m (tab + 18 * Z.of_nat (length t) + 15) [CB 1 [Z_to_bv 8 0]; CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]] ->
  bytes_at rsegs m tab bt -> rw_cells rsegs m n [C4 (Z_to_bv 64 (Z.of_nat (length t)))] ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 vid) w10 x11 x12 x13 x14 x15 x16
             x17 (Z_to_bv 64 tab) (Z_to_bv 64 par) (Z_to_bv 64 18) (Z_to_bv 64 max) x22
             (Z_to_bv 64 (Z.of_nat (length t))) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16690) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w10 x22 x24 x25 x26 x27 s15 LT HEX E10 E15
    ((j0 & FR) & ST & MU & WM & MI) B15 Z3 BT NC.
  subst w10.
  assert (L15 : length s15 = 15%nat)
    by (subst s15; unfold stpn_result, stpn_k; rewrite length_app, length_firstn, repeat_length; lia).
  pose proof HAT as A1. pose proof HnT as A2. pose proof HnA as A4. unfold apart in A1, A2, A4.
  pose proof (rw_cells_bound _ _ _ _ Z3) as B3. cbn [cells_size csize Nat.add] in B3.
  step.  (* sh s1,16(a0): tab[*n].vid *)
  step. rewrite (sx32_small (Z.of_nat (length t))) by lia.  (* lw a1,0(s0) *)
  step. ul. rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).  (* addiw a0,a1,1 *)
  step. rewrite lts_small by lia.  (* blt a0,a1 -> TRAP *)
  destruct (Z.ltb_spec (Z.of_nat (length t) + 1) (Z.of_nat (length t))) as [X|_]; [lia|]. cbv iota.
  step.  (* sw a0,0(s0): *n + 1 *)
  step. step.  (* s4 = 1; j EPI *)
  eapply epi; rewrite ?(vlan_add_app t max p vid HEX LT); cbn [fst snd].
  - weq.
  - rewrite vtab_W_app. exact (conj (ex_intro _ j0 FR) (conj ST (conj MU (conj WM MI)))).
  - exists (bt ++ (s15 ++ [Z_to_bv 8 0] ++ le2 (Z_to_bv 64 vid))). split.
    + apply bytes_at_app. split; [exact BT|]. rewrite Lbt.
      replace (tab + Z.of_nat (18 * length t)) with (tab + 18 * Z.of_nat (length t)) by lia.
      apply bytes_at_app. split; [exact B15|]. rewrite L15.
      destruct Z3 as [[_ Z3b] _]. cbn [cells_bytes cbytes] in Z3b. rewrite app_nil_r in Z3b.
      replace (tab + 18 * Z.of_nat (length t) + Z.of_nat 15) with (tab + 18 * Z.of_nat (length t) + 15) by lia.
      exact Z3b.
    + apply rtab_enc_snoc; [exact HET|]. subst s15. unfold stpn_result, stpn_k.
      apply new_entry_enc; assumption.
  - rewrite length_app. cbn [length].
    replace (Z.of_nat (length t + 1)) with (Z.of_nat (length t) + 1) by lia. exact NC.
Qed.

(** 0x1665c `jal strncpy` with a0 = &tab[*n], a1 = parent, a2 = 15; then *n reloaded, a0 = &tab[*n] and its three
    checks. *)
Lemma uapp_sn : forall m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 w10 w11 w12 x22 x24 x25 x26 x27 : word),
  Z.of_nat (length t) < max -> existsb (vmatch vid p) t = false ->
  w10 = Z_to_bv 64 (tab + 18 * Z.of_nat (length t)) -> w11 = Z_to_bv 64 par -> w12 = Z_to_bv 64 15 ->
  frm Wapp m ->
  rw_cells rsegs m (tab + 18 * Z.of_nat (length t)) [CB 15 (repeat (Z_to_bv 8 0) 15)] ->
  rw_cells rsegs m (tab + 18 * Z.of_nat (length t) + 15) [CB 1 [Z_to_bv 8 0]; CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]] ->
  bytes_at rsegs m tab bt -> rw_cells rsegs m n [C4 (Z_to_bv 64 (Z.of_nat (length t)))] ->
  bytes_at rsegs m par (pb ++ Z_to_bv 8 0 :: psl) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 vid) w10 w11 w12 x13 x14 x15 x16
             x17 (Z_to_bv 64 tab) (Z_to_bv 64 par) (Z_to_bv 64 18) (Z_to_bv 64 max) x22
             (Z_to_bv 64 (Z.of_nat (length t))) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1665c) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 w10 w11 w12 x22 x24 x25 x26 x27 LT HEX E10 E11 E12
    ((j0 & FR) & ST & MU & WM & MI) Z15 Z3 BT NC PB.
  subst w10 w11 w12.
  pose proof HAT as A1. pose proof HnT as A2. pose proof HPT as A3. pose proof HnA as A4. pose proof HPA as A5.
  unfold apart in A1, A2, A3, A4, A5.
  pose proof (rw_cells_bound _ _ _ _ Z15) as B15. cbn [cells_size csize Nat.add] in B15.
  pose proof (bytes_at_bound _ _ _ _ PB) as BP. rewrite length_app in BP. cbn [length] in BP.
  pose proof (rw_cells_bound _ _ _ _ Z3) as B3. cbn [cells_size csize Nat.add] in B3.
  step.  (* jal strncpy *)
  eapply evt_cut.
  { eapply HSN with (str := pb) (slack := psl) (bs := repeat (Z_to_bv 8 0) 15) (lo := lo); ul.
    - exact (u8arr_of_rw_cells rsegs m _ _ _ Z15).
    - reflexivity.
    - exact PB.
    - exact HPN.
    - exact HPS.
    - exact ST.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact MI. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> &
              MU3 & WM3 & MI3 & ST3 & U3 & PB3).
  rewrite ret_pc_even by (try lia; reflexivity).
  ulh MU3. ulh ST3. ulh U3. change (Z.to_nat 15) with 15%nat in U3.
  pose proof (rw_cells_transport rsegs _ m m3 _ _ FR MU3 WM3) as FR3. djh FR3.
  pose proof (bytes_at_transport rsegs _ m m3 _ _ BT MU3) as BT3. rewrite Lbt in BT3. djh BT3.
  pose proof (rw_cells_transport rsegs _ m m3 _ _ NC MU3 WM3) as NC3. djh NC3.
  pose proof (rw_cells_transport rsegs _ m m3 _ _ Z3 MU3 WM3) as Z33. djh Z33.
  assert (MU3' : munch Wapp m0 m3).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU3].
    unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _). repeat split; lia. }
  pose proof (wmono_trans rsegs m0 m m3 WM WM3) as WM3'.
  clear FR BT NC Z3 Z15 PB MU WM MI MU3 WM3 PB3.
  step. rewrite (sx32_small (Z.of_nat (length t))) by lia.  (* lw a1,0(s0) *)
  step. step. step.  (* a0 = 18; a0 = *n * 18; a0 = tab + a0 *)
  ul. replace (tab + Z.of_nat (length t) * 18) with (tab + 18 * Z.of_nat (length t)) by lia.
  step. ntk.  (* beqz a0 -> TRAP *)
  step. rewrite au_slti0 by lia.  (* slti a1,a1,0 *)
  step. rewrite au_sltu_ge by lia.  (* sltu a2,a0,s2 *)
  step. step. step. ntk.  (* xor; xori; beqz a1 -> TRAP *)
  step. rewrite au_land1 by (try lia; Z.div_mod_to_equations; lia).  (* andi a1,a0,1 *)
  step. ntk.  (* bnez a1 -> TRAP *)
  eapply uapp_tail; [exact LT | exact HEX | weq | reflexivity | | exact (proj1 U3) | exact Z33 | exact BT3
                    | exact NC3].
  exact (conj (ex_intro _ j0 FR3) (conj ST3 (conj MU3' (conj WM3' MI3)))).
Qed.

(** 0x16624 `jal memset` with a0 = &tab[*n], a1 = 0, a2 = 18; then *n reloaded, a0 = &tab[*n] and its three checks,
    a2 = 15, a1 = parent. *)
Lemma uapp_ms : forall m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 w10 w11 w12 w20 x22 x24 x25 x26 x27
                         : word),
  Z.of_nat (length t) < max -> existsb (vmatch vid p) t = false ->
  w10 = Z_to_bv 64 (tab + 18 * Z.of_nat (length t)) -> w11 = Z_to_bv 64 0 -> w12 = Z_to_bv 64 18 ->
  w20 = Z_to_bv 64 18 -> frm [(Sp - 112, Sp)] m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 vid) w10 w11 w12 x13 x14 x15 x16
             x17 (Z_to_bv 64 tab) (Z_to_bv 64 par) w20 (Z_to_bv 64 max) x22
             (Z_to_bv 64 (Z.of_nat (length t))) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x16624) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 w10 w11 w12 w20 x22 x24 x25 x26 x27 LT HEX E10 E11 E12
    E20 FRM.
  subst w10 w11 w12 w20.
  pose proof (frm_bt m FRM) as BT. pose proof (frm_n m FRM) as NC. pose proof (frm_par m FRM) as PB.
  pose proof (frm_free m FRM) as FC.
  (* tab[*n]: the first 18 free bytes *)
  assert (FC18 : rw_cells rsegs m (tab + 18 * Z.of_nat (length t)) [CB 18 (firstn 18 free)]).
  { assert (S18 : sum_nat [18%nat; (Z.to_nat (18 * (max - Z.of_nat (length t))) - 18)%nat] =
                  Z.to_nat (18 * (max - Z.of_nat (length t)))) by (cbn [sum_nat]; lia).
    pose proof (rw_cells_split_CB rsegs m (tab + 18 * Z.of_nat (length t)) []
                  (Z.to_nat (18 * (max - Z.of_nat (length t)))) free [] _ FC S18) as H.
    cbn [app mk_CB_cells] in H. exact (proj1 (rw_cells_cons rsegs m _ _ _ H)). }
  destruct FRM as ((j0 & FR) & ST & MU & WM & MI).
  assert (MUa : munch Wapp m0 m).
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _).
    split; [lia | exact I]. }
  clear MU FC.
  pose proof HAT as A1. pose proof HnT as A2. pose proof HPT as A3. unfold apart in A1, A2, A3.
  pose proof (rw_cells_bound _ _ _ _ FC18) as B18. cbn [cells_size csize Nat.add] in B18.
  step.  (* jal memset *)
  eapply evt_cut.
  { eapply HMS with (junk := firstn 18 free); [|exact MI]. ul. exact FC18. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> &
              MU2 & WM2 & MI2 & RW2).
  rewrite ret_pc_even by (try lia; reflexivity).
  ulh MU2. ulh RW2.
  change (Z.to_nat 18) with 18%nat in RW2. change (0 mod 256) with 0 in RW2.
  destruct (zero18_split rsegs m2 _ _ RW2) as [Z15 Z3].
  pose proof (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2) as FR2. djh FR2.
  pose proof (stk_transport_disjoint rsegs _ m m2 lo (Sp + -112) ST MU2 WM2) as ST2. djh ST2.
  pose proof (bytes_at_transport rsegs _ m m2 _ _ BT MU2) as BT2. rewrite Lbt in BT2. djh BT2.
  pose proof (rw_cells_transport rsegs _ m m2 _ _ NC MU2 WM2) as NC2. djh NC2.
  pose proof (bytes_at_transport rsegs _ m m2 _ _ PB MU2) as PB2. rewrite length_app in PB2. cbn [length] in PB2.
  djh PB2.
  assert (MU2' : munch Wapp m0 m2).
  { eapply munch_trans; [exact MUa|]. eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _). repeat split; lia. }
  pose proof (wmono_trans rsegs m0 m m2 WM WM2) as WM2'.
  clear FR ST BT NC PB MUa WM MI MU2 WM2 RW2 FC18.
  step. rewrite (sx32_small (Z.of_nat (length t))) by lia.  (* lw a1,0(s0) *)
  step. step.  (* a0 = *n * 18; a0 = tab + a0 *)
  ul. replace (tab + Z.of_nat (length t) * 18) with (tab + 18 * Z.of_nat (length t)) by lia.
  step. ntk.  (* beqz a0 -> TRAP *)
  step. rewrite au_slti0 by lia.  (* slti a1,a1,0 *)
  step. rewrite au_sltu_ge by lia.  (* sltu a2,a0,s2 *)
  step. step. step. ntk.  (* xor; xori; beqz a1 -> TRAP *)
  step. rewrite au_land1 by (try lia; Z.div_mod_to_equations; lia).  (* andi a1,a0,1 *)
  step. ntk.  (* bnez a1 -> TRAP *)
  step. step.  (* a2 = 15; a1 = parent *)
  eapply uapp_sn; [exact LT | exact HEX | weq | weq | weq | | exact Z15 | exact Z3 | exact BT2 | exact NC2
                  | exact PB2].
  exact (conj (ex_intro _ j0 FR2) (conj ST2 (conj MU2' (conj WM2' MI2)))).
Qed.

(** 0x165e8, the search done without a match: `bge s7,s5` -> -1, else the checks of tab + 18 *n and the append. *)
Lemma after : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w20 w22 w24 w25 w26 w27 : word),
  existsb (vmatch vid p) t = false -> w20 = Z_to_bv 64 (-1) -> frm [(Sp - 112, Sp)] m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 vid) x10 x11 x12 x13 x14 x15 x16
             x17 (Z_to_bv 64 tab) (Z_to_bv 64 par) w20 (Z_to_bv 64 max) w22 (Z_to_bv 64 (Z.of_nat (length t))) w24
             w25 w26 w27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x165e8) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w20 w22 w24 w25 w26 w27 HEX E20 FRM.
  pose proof (frm_free m FRM) as FC. pose proof (rw_cells_bound _ _ _ _ FC) as FB.
  cbn [cells_size csize] in FB. clear FC.
  step. rewrite lts_small by lia.
  destruct (Z.ltb_spec (Z.of_nat (length t)) max) as [LT|GE]; cbn [negb]; cbv iota.
  - (* room: the checks, then append *)
    step. step. step.  (* a0 = 18; a0 = *n * 18; a0 = a0 + tab *)
    ul. replace (Z.of_nat (length t) * 18 + tab) with (tab + 18 * Z.of_nat (length t)) by lia.
    step. ntk.  (* beqz a0 -> TRAP *)
    step. rewrite au_sltu_ge by lia.  (* sltu a0,a0,s2 *)
    step. rewrite au_slti0 by lia.  (* slti a1,s7,0 *)
    step. step. step. ntk.  (* xor; xori; beqz a0 -> TRAP *)
    step. step. step. step. step.  (* s4 = 18; a0 = tab + 18 *n; a2 = 18; a1 = 0 *)
    eapply uapp_ms; [exact LT | exact HEX | weq | weq | weq | weq | exact FRM].
  - (* full: -1 *)
    eapply keep_exit; [exact (vlan_add_full t max p vid HEX GE) | exact E20 | exact FRM].
Qed.

(** The search loop 0x165b8 at entry i (k = *n - i entries left): s6 = &tab[i], s8 = 18 i, s9 = ~tab, s10 = 0
    (tab & 1), s11 = k; entries 0 .. i-1 did not match. *)
Lemma sloop : forall k i m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w20 w22 w24 w25 w26 w27
                            : word),
  (i + k = length t)%nat -> (0 < k)%nat ->
  w20 = Z_to_bv 64 (-1) -> w22 = Z_to_bv 64 (tab + 18 * Z.of_nat i) -> w24 = Z_to_bv 64 (18 * Z.of_nat i) ->
  bv_unsigned w25 = 18446744073709551615 - tab -> w26 = Z_to_bv 64 0 -> w27 = Z_to_bv 64 (Z.of_nat k) ->
  existsb (vmatch vid p) t = existsb (vmatch vid p) (skipn i t) -> frm [(Sp - 112, Sp)] m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 vid) x10 x11 x12 x13 x14 x15 x16
             x17 (Z_to_bv 64 tab) (Z_to_bv 64 par) w20 (Z_to_bv 64 max) w22 (Z_to_bv 64 (Z.of_nat (length t))) w24
             w25 w26 w27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x165b8) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w20 w22 w24 w25 w26
    w27 Hik Hk E20 E22 E24 E25 E26 E27 HEX FRM; [lia|].
  subst w22 w24 w26 w27.
  assert (Hi : (i < length t)%nat) by lia.
  destruct (rtab_entry rsegs m tab t bt i (frm_bt m FRM) HET Hi) as (RD1 & RV1 & sx & BX & ZX & NX).
  pose proof (frm_parz m FRM) as BP. pose proof (bytes_at_bound _ _ _ _ BP) as BPd.
  rewrite length_app in BPd. cbn [length] in BPd.
  pose proof (bytes_at_bound _ _ _ _ HBT) as TB. rewrite Lbt in TB.
  rewrite (existsb_skipn_S (vmatch vid p) t i ([], 0) Hi) in HEX.
  step. ntk.  (* bltu s9,s8 -> TRAP: tab + 18 i does not wrap *)
  step. ntk.  (* bnez s10 -> TRAP: tab is even *)
  step. rewrite (zx16_small _ RV1).
  step. rewrite sq_eqb_lit by lia.
  destruct (Z.eqb_spec (snd (nth i t ([], 0))) vid) as [EV|EV]; cbn [negb]; cbv iota.
  - (* the vids agree: strcmp(tab[i].parent, parent) *)
    step. step. step.
    eapply evt_cut.
    { eapply HSC with (sx := sx) (sy := pb); ul; assumption. }
    intros ms' (r & y11 & y12 & y13 & -> & Hr).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (CMP : sx = pb <-> SegModel.strcmp (fst (nth i t ([], 0))) p = 0).
    { rewrite <- ZX, <- HPZ. symmetry. apply SegBridge.bridge_strcmp; assumption. }
    step.
    destruct (bv_eqb r (Z_to_bv 64 0)) eqn:K; cbv iota.
    + (* equal parents: a duplicate, 0 *)
      apply sq_eqb_true in K. apply Hr, CMP in K.
      assert (HD : existsb (vmatch vid p) t = true).
      { rewrite HEX. unfold vmatch. rewrite EV, Z.eqb_refl, K. reflexivity. }
      step.
      eapply keep_exit; [exact (vlan_add_dup t max p vid HD) | weq | exact FRM].
    + (* the next entry *)
      apply sq_eqb_false in K.
      assert (NM : vmatch vid p (nth i t ([], 0)) = false).
      { unfold vmatch. rewrite EV, Z.eqb_refl. cbn [andb]. apply Z.eqb_neq. intros E. apply K, Hr, CMP, E. }
      rewrite NM in HEX. cbn [orb] in HEX.
      step. step. step. step.
      rewrite sq_eqb_lit by lia.
      destruct (Z.eqb_spec (Z.of_nat (S k) + -1) 0) as [J0|J0]; cbn [negb]; cbv iota.
      * assert (k = 0%nat) by lia. subst k.
        replace (S i) with (length t) in HEX by lia. rewrite skipn_all in HEX. cbn [existsb] in HEX.
        eapply after; [exact HEX | exact E20 | exact FRM].
      * eapply (IH (S i)); [lia | lia | exact E20 | weq | weq | exact E25 | reflexivity | weq | exact HEX
                           | exact FRM].
  - (* the vids differ: the next entry *)
    assert (NM : vmatch vid p (nth i t ([], 0)) = false).
    { unfold vmatch. rewrite (proj2 (Z.eqb_neq _ _) EV). reflexivity. }
    rewrite NM in HEX. cbn [orb] in HEX.
    step. step. step. step.
    rewrite sq_eqb_lit by lia.
    destruct (Z.eqb_spec (Z.of_nat (S k) + -1) 0) as [J0|J0]; cbn [negb]; cbv iota.
    + assert (k = 0%nat) by lia. subst k.
      replace (S i) with (length t) in HEX by lia. rewrite skipn_all in HEX. cbn [existsb] in HEX.
      eapply after; [exact HEX | exact E20 | exact FRM].
    + eapply (IH (S i)); [lia | lia | exact E20 | weq | weq | exact E25 | reflexivity | weq | exact HEX
                         | exact FRM].
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 tab) (Z_to_bv 64 max) (Z_to_bv 64 n)
             (Z_to_bv 64 par) (Z_to_bv 64 vid) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16530) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses the later lemmas use: take them
     first. *)
  pose proof (sloop (length t) 0) as LP. pose proof after as AF.
  pose proof (munch_refl [(Sp - 112, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof HnA as A4. unfold apart in A4.
  pose proof (bytes_at_bound _ _ _ _ HBT) as TB. pose proof (bytes_at_bound _ _ _ _ HPB) as PBd.
  pose proof (rw_cells_bound _ _ _ _ HN) as NB. cbn [cells_size csize Nat.add] in NB.
  clear HBT HFR HPB.
  destruct (stk_carve rsegs m0 lo Sp 112 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 112) with 112 in ST1, FR.
  replace (Sp - 112) with (Sp + -112) in ST1, FR by lia.
  do 14 step.  (* addi sp; thirteen sd *)
  step.  (* s4 = -1 *)
  step. rewrite sq_eqb_lit by lia. replace (tab =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step. rewrite sq_eqb_lit by lia. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step. rewrite sq_eqb_lit by lia. replace (par =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota.
  step.  (* s2 = tab *)
  step. rewrite au_land3 by lia.  (* andi a0,s0,3 *)
  step. rewrite sq_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.  (* bnez a0 -> TRAP *)
  step. step.  (* s1 = vid; s5 = max *)
  step. rewrite (sx32_small (Z.of_nat (length t))) by lia.  (* lw s7,0(s0) *)
  step.  (* blez s7 *)
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (Z.of_nat (length t) <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r.
  destruct (Z.ltb_spec 0 (Z.of_nat (length t))) as [P|P]; cbn [negb]; cbv iota.
  - do 7 step.  (* s8 = 0; s9 = ~tab; s10 = tab & 1; s11 = *n; s6 = tab *)
    eapply LP; [lia | lia | weq | weq | weq | apply reac_segconf_find.fu_not; lia
               | f_equal; apply au_land1; [lia | Z.div_mod_to_equations; lia]
               | f_equal; apply reac_segconf_find.fu_s4; lia | reflexivity |].
    refine (conj _ (conj _ (conj _ (conj _ _)))); [eexists|..]; eassumption.
  - (* no entry *)
    eapply AF; [| weq | refine (conj _ (conj _ (conj _ (conj _ _)))); [eexists|..]; eassumption].
    destruct t as [|e l]; [reflexivity | cbn [length] in P; lia].
Qed.

End Add.

Theorem reac_declared_vlan_add_holds :
  strcmp_contract -> memset_contract -> strncpy_contract -> reac_declared_vlan_add_contract.
Proof.
  intros HSC HMS HSN. unfold reac_declared_vlan_add_contract, add_pre, vtab_pre, REAC_DECLARED_VLAN_ADD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo t p
    ((Htab0 & Htab16 & (bt & HBT & HET) & HLm & (free & HFR) & HAT & Hn0 & Hn4 & HN & HnA & HnT) &
     Hpar0 & HCS & HPA & HPT & HV & (ST & HK & H16 & HW) & MI).
  destruct (cstr_cut _ _ _ _ HCS) as (pb & psl & HPB & HPZ & HPN0 & HPN & HPL & HPS & HPS8).
  pose proof (proj1 HET) as Lbt.
  unfold RVLAN_SIZE in *. unfold ADD_STACK in HK.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a2) as Ra2.
  pose proof (u64_range a3) as Ra3.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1. pose proof (Z_to_bv_lit_self a2) as Ea2.
  pose proof (Z_to_bv_lit_self a3) as Ea3. pose proof (Z_to_bv_lit_self a4) as Ea4.
  set (Sp := bv_unsigned sp) in *. set (tab := bv_unsigned a0) in *. set (max := bv_unsigned a1) in *.
  set (n := bv_unsigned a2) in *. set (par := bv_unsigned a3) in *. set (vid := bv_unsigned a4) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
  clearbody Sp tab max n par vid. clear Esp Ea0 Ea1 Ea2 Ea3 Ea4.
  eapply body; first [eassumption | lia].
Qed.
