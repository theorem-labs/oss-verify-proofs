(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype F_syscalls F_errno_location F_strtol H_scanner_get_token H_vfmatch_A HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Ltac sstep := step; fix_lit_store.

Lemma strtol_call : forall (qq lo Ss E : Z) (str ejunk : list byte) (errv canary : word)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at rsegs m Ss (str ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs m E [CB 8 ejunk] -> (E <> 0)%Z ->
  rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
  stk rsegs m lo qq -> mem_inv rsegs m ->
  (lo <= qq - STRTOL_DEPTH)%Z -> (ssp_guard + 8 <= lo)%Z -> (0 <= qq < 2^63)%Z ->
  (4096 + 164 <= bv_unsigned tp)%Z ->
  (4096 <= Ss)%Z -> (Ss + 2^41 <= 2^63)%Z -> (Z.of_nat (length str) + 1 <= 2^40)%Z ->
  (Ss + Z.of_nat (length str) + 1 <= qq - STRTOL_DEPTH \/ qq <= Ss)%Z ->
  (Ss + Z.of_nat (length str) + 1 <= got_ssp \/ got_ssp + 8 <= Ss)%Z -> (Ss + Z.of_nat (length str) + 1 <= ssp_guard \/ ssp_guard + 8 <= Ss)%Z ->
  (bv_unsigned tp - 164 + 4 <= lo \/ qq <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= Ss \/ Ss + Z.of_nat (length str) + 1 <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z -> (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z ->
  ((E + 8 <= lo \/ qq <= E) /\ (E + 8 <= Ss \/ Ss + Z.of_nat (length str) + 1 <= E) /\
   (E + 8 <= bv_unsigned tp - 164 \/ bv_unsigned tp - 164 + 4 <= E) /\
   (E + 8 <= got_ssp \/ got_ssp + 8 <= E) /\ (E + 8 <= ssp_guard \/ ssp_guard + 8 <= E) /\ 0 <= E /\ E + 8 <= 2^64)%Z ->
  a0 = wz Ss -> a1 = wz E -> a2 = wz 16 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (errv' : word) (k : Z),
      ms' = MS (mkR ra (wz qq) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(qq - 528, qq); (E, E + 8); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo qq
      /\ bytes_at rsegs m' Ss (str ++ [Z_to_bv 8 0])
      /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary]
      /\ rw_cells rsegs m' (bv_unsigned tp - 164) [C4 errv']
      /\ (0 <= k <= Z.of_nat (length str))%Z
      /\ rw_cells rsegs m' E [C8 (Z_to_bv 64 (Ss + k))])
    (MS (mkR ra (wz qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz strtol_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros STR EC EN ERR GOT CAN ST MI LO GLO QQ TP S4 SHI LEN D1 D2 D3 D4 D5 D6 D7 DE -> -> ->.
  assert (E0 : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (strtol_proof ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Ss str E 16 ejunk errv canary lo);
      rewrite ?E0; eauto; try lia. }
  intros ms' P. unfold strtol_post, STRTOL_DEPTH in P. rewrite !E0 in P. destruct_exs P.
  destruct P as (-> & MU & WM & MI' & ST' & STR' & GOT' & CAN' & ERR' & HK & EC').
  repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
  repeat (split; [eassumption|]). apply EC'. exact EN.
Qed.

Lemma e_slot_merge : forall m a (ty : word) (j : list byte),
  rw_cells rsegs m a [C4 ty] -> rw_cells rsegs m (a + 4) [CB 8 j] ->
  exists ej j4, rw_cells rsegs m a [CB 8 ej] /\ rw_cells rsegs m (a + 8) [CB 4 j4].
Proof.
  intros m a ty j H1 H2.
  pose proof (proj2 (rw_cells_app rsegs m a [C4 ty] [CB 8 j]) (conj H1 H2)) as H. cbn [app] in H.
  pose proof (rw_cells_merge rsegs m a [] [C4 ty; CB 8 j] [] H) as M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  assert (L : length j = 8%nat) by (destruct H2 as [[W _] _]; cbn in W; LiaTuning.ctauto).
  apply (rw_cells_split_CB rsegs m a [] 12 _ [] [8%nat; 4%nat]) in M; [| reflexivity]. cbn [app mk_CB_cells] in M.
  destruct (proj1 (rw_cells_app rsegs m a [CB 8 _] [CB 4 _]) M) as [M1 M2]. cbn [cells_size csize Nat.add] in M2.
  eexists _, _. split; [exact M1| exact M2].
Qed.

Lemma e_slot_unmerge : forall m a (w : word) (j4 : list byte),
  rw_cells rsegs m a [C8 w] -> rw_cells rsegs m (a + 8) [CB 4 j4] ->
  exists (ty : word) j, rw_cells rsegs m a [C4 ty] /\ rw_cells rsegs m (a + 4) [CB 8 j].
Proof.
  intros m a w j4 H1 H2.
  pose proof (proj2 (rw_cells_app rsegs m a [C8 w] [CB 4 j4]) (conj H1 H2)) as H. cbn [app] in H.
  pose proof (rw_cells_merge rsegs m a [] [C8 w; CB 4 j4] [] H) as M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  assert (L : length j4 = 4%nat) by (destruct H2 as [[W _] _]; cbn in W; LiaTuning.ctauto).
  apply (rw_cells_split_CB rsegs m a [] 12 _ [] [4%nat; 8%nat]) in M. 2:{ reflexivity. } cbn [app mk_CB_cells] in M.
  apply (rw_cells_CB_C4 rsegs m a []) in M. cbn [app] in M.
  destruct (proj1 (rw_cells_app rsegs m a [C4 _] [CB 8 _]) M) as [M1 M2]. cbn [cells_size csize Nat.add] in M2.
  eexists _, _. split; [exact M1| exact M2].
Qed.

Lemma tok_cstr : forall m A bs (cur len : Z),
  bytes_at rsegs m A bs -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> (0 <= cur <= len)%Z ->
  bytes_at rsegs m (A + cur) (firstn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs) ++ [Z_to_bv 8 0]).
Proof.
  intros m A bs cur len B N HC. pose proof (nth_error_lt _ _ _ N) as L.
  rewrite <- (firstn_skipn (Z.to_nat cur) bs) in B. apply bytes_at_app in B. destruct B as [_ B].
  rewrite firstn_length, Nat.min_l, Z2Nat.id in B by lia.
  rewrite <- (firstn_skipn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs)) in B. rewrite skipn_skipn in B.
  replace (Z.to_nat (len - cur) + Z.to_nat cur)%nat with (Z.to_nat len) in B by lia.
  destruct (skipn (Z.to_nat len) bs) as [|z rest] eqn:SK.
  { exfalso. apply (f_equal (@length byte)) in SK. rewrite skipn_length in SK. cbn in SK. lia. }
  assert (Hz : z = Z_to_bv 8 0).
  { rewrite <- (firstn_skipn (Z.to_nat len) bs) in N. rewrite nth_error_app2 in N by (rewrite firstn_length; lia).
    rewrite firstn_length, Nat.min_l, Nat.sub_diag, SK in N by lia. cbn in N. congruence. }
  subst z. change (?f ++ Z_to_bv 8 0 :: rest) with (f ++ [Z_to_bv 8 0] ++ rest) in B. rewrite app_assoc in B.
  apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

Ltac xor_ok :=
  lazymatch goal with |- context [Z.lxor (Z.b2z (0 <? ?X)) (Z.b2z (?Y <? 1))] =>
    replace (Z.lxor (Z.b2z (0 <? X)) (Z.b2z (Y <? 1))) with 1;
    [| destruct (Z.ltb_spec 0 X); destruct (Z.ltb_spec Y 1); try lia; reflexivity ]
  end.

Section VF3.
Context {HCEIL : HasCeiling}.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation headst := (headst q S cur0). Notation contst := (contst q S cur0). Notation exitst := (exitst q S cur0).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q).
  Notation F0 := (F0 q). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).
  Ltac sgtcall T TY cur := sgtcall_ (q + -208)%Z lo S T TY MB A cur len cap bs.

  Definition XX (cur P : Z) (tp canary : word) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    exists (pv' e' : word), rw_cells rsegs m' P [C4 pv'] /\ rw_cells rsegs m' (bv_unsigned tp - 164) [C4 e']
      /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary]
      /\ (r = PARSE_OK -> exists v l, pv' = wz v /\ 0 <= v < 2^31 /\ 1 <= l /\ cur' = cur + l /\ cur' < len)%Z.

  Notation WX P tp := [(q - 736, q - 104); (S + 8, S + 16); (P, P + 4); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z.

  Ltac xfin := unfold XX; do 2 eexists; repeat (split; [eassumption|]); unfold PARSE_OK; first [intros; exfalso; lia | idtac].

  #[using="VOK"] Lemma x_body : forall (fp G cs cur P : Z) (pv errv canary : word) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z ->
    rw_cells rsegs m G [C8 (wz P)] -> rw_cells rsegs m P [C4 pv] -> (q + 64 <= P /\ P + 4 <= MB)%Z -> (P mod 4 = 0)%Z ->
    (lo + 736 <= q)%Z -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    (4096 + 164 <= bv_unsigned tp)%Z -> (bv_unsigned tp mod 4 = 0)%Z -> (bv_unsigned tp - 160 <= lo)%Z -> (ssp_guard + 8 <= lo)%Z -> (got_ssp + 8 <= lo)%Z ->
    (4096 <= A)%Z -> (A + cap + 2^41 < 2^63)%Z -> (cap + 2 <= 2^40)%Z ->
    (bv_unsigned tp - 160 <= A \/ A + Z.of_nat (length bs) <= bv_unsigned tp - 164)%Z ->
    (got_ssp + 8 <= A \/ A + Z.of_nat (length bs) <= got_ssp)%Z -> (ssp_guard + 8 <= A \/ A + Z.of_nat (length bs) <= ssp_guard)%Z ->
    (bv_unsigned tp - 160 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z ->
    (bv_unsigned tp - 160 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WX P tp) (XX cur P tp canary) (fun _ => False) m)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) (wz 4) (wz 82836%Z) (wz 88) x13 x14 x15 x16 x17
               (wz (fp + 2)) (wz 120) (wz (q + -152)) (wz 37) (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
          F (wz 82836%Z) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR GC PCH PL PAL
      DEEP NULT ERR GOT CAN TP TPAL TPLO GLO GOLO A4 AHI2 CAP40 DA1 DA2 DA3 DG1 DG2.
    unfold SCc, MBc, mbuf_cells, MEMBUF_DEF_SIZE_INC, BUFc, F0, F36, F40, F56, F72, F76, F84, F88 in *. dex.
    pose proof (munch_refl (WX P tp) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. assert (LENL : (len < Z.of_nat (length bs))%Z) by (pose proof (nth_error_lt _ _ _ NULT); lia).
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    uwalk_lia_to 83728%Z.
    step. sgtcall (q + -120) (q + -124) cur. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    -   clear CRL. uwalk_lia_to 83748%Z.
      if_cases K1; zify_cond K1.
      + uwalk_lia_to 82344%Z. dfinish 5 cur. xfin.
      + uwalk_lia_to 83748%Z.
        zstep. call errno_location_spec. 1: lia. 1: exact MI.
        uwalk_lia_to 83764%Z. ubr. uwalk_lia_to 83780%Z. zstep.
        replace (q + -132)%Z with (q + -136 + 4)%Z in FR76 by lia.
        destruct (e_slot_merge _ _ _ _ FR72 FR76) as (ej & j4 & E8 & E4). clear FR72 FR76.
        replace (q + -136 + 8)%Z with (q + -128)%Z in E4 by lia.
        pose proof (tok_cstr _ A bs cur len BUF NULT ltac:(lia)) as CSTR.
        assert (LSTR : Z.of_nat (length (firstn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs))) = (len - cur)%Z).
        { rewrite length_firstn, length_skipn. clear - CUR CUR0 LENL. lia. }
        call (strtol_call (q + -208) lo (A + cur) (q + -136) (firstn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs)) ej).
        all: rewrite ?LSTR.
        all: side (first [exact CSTR | exact E8 | exact MI | reflexivity | eassumption | unfold STRTOL_DEPTH; lia]).
        rename MI0 into MI. rename PC into ST. try clear GOT; try clear CAN. rename PC1 into GOT. rename PC2 into CAN. rename PC3 into ERR. rename PC4 into HK. rename POST into E8.
        rewrite LSTR in HK.
        lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename a into num end.
        pose proof (word_lt64 num) as NB.
        uwalk_lia_to 83832%Z.
        if_cases K2; zify_cond K2.
        * uwalk_lia_to 82344%Z. ubr. uwalk_lia_to 82344%Z. replace (q + -128)%Z with (q + -136 + 8)%Z in E4 by lia. destruct (e_slot_unmerge _ _ _ _ E8 E4) as (ty72 & j76 & FR72 & FR76). clear E8 E4. replace (q + -136 + 4)%Z with (q + -132)%Z in FR76 by lia. dfinish 5 cur. xfin.
        * uwalk_lia_to 82344%Z. xor_ok. uwalk_lia_to 82344%Z.
          if_cases K3; zify_cond K3.
          -- uwalk_lia_to 82344%Z. ubr. uwalk_lia_to 82344%Z. replace (q + -128)%Z with (q + -136 + 8)%Z in E4 by lia. destruct (e_slot_unmerge _ _ _ _ E8 E4) as (ty72 & j76 & FR72 & FR76). clear E8 E4. replace (q + -136 + 4)%Z with (q + -132)%Z in FR76 by lia. dfinish 4 (cur + tlz)%Z. xfin.
             intros _. exists (bv_unsigned num), tlz. repeat split; try reflexivity; try lia.
             all: try (apply STRICT; left; unfold TT_IDENTIFIER; lia).
             ++ symmetry. apply Z_to_bv_bv_unsigned.
             ++ destruct (Z.lt_ge_cases (bv_unsigned num) (2^31)) as [Hl|Hg]; [exact Hl| exfalso].
                rewrite Z.shiftr_div_pow2 in K2 by lia. assert (2^31 / 2^31 <= bv_unsigned num / 2^31)%Z by (apply Z.div_le_mono; lia).
                rewrite Z.div_same in H by lia. lia.
          -- uwalk_lia_to 82344%Z. ubr. uwalk_lia_to 82344%Z. replace (q + -128)%Z with (q + -136 + 8)%Z in E4 by lia. destruct (e_slot_unmerge _ _ _ _ E8 E4) as (ty72 & j76 & FR72 & FR76). clear E8 E4. replace (q + -136 + 4)%Z with (q + -132)%Z in FR76 by lia. dfinish 5 cur. xfin.
    - uwalk_lia_to 82344%Z. dfinish rr cur. xfin.
  Qed.

  #[using="VOK"] Lemma dir_x : forall (fp G cs cur P : Z) (b2 : byte) (pv errv canary : word) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 120 ->
    rw_cells rsegs m G [C8 (wz P)] -> rw_cells rsegs m P [C4 pv] -> (q + 64 <= P /\ P + 4 <= MB)%Z -> (P mod 4 = 0)%Z ->
    (lo + 736 <= q)%Z -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    (4096 + 164 <= bv_unsigned tp)%Z -> (bv_unsigned tp mod 4 = 0)%Z -> (bv_unsigned tp - 160 <= lo)%Z -> (ssp_guard + 8 <= lo)%Z -> (got_ssp + 8 <= lo)%Z ->
    (4096 <= A)%Z -> (A + cap + 2^41 < 2^63)%Z -> (cap + 2 <= 2^40)%Z ->
    (bv_unsigned tp - 160 <= A \/ A + Z.of_nat (length bs) <= bv_unsigned tp - 164)%Z ->
    (got_ssp + 8 <= A \/ A + Z.of_nat (length bs) <= got_ssp)%Z -> (ssp_guard + 8 <= A \/ A + Z.of_nat (length bs) <= ssp_guard)%Z ->
    (bv_unsigned tp - 160 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z ->
    (bv_unsigned tp - 160 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WX P tp) (XX cur P tp canary) (fun _ => False) m)
        (headst gp tp F fc fp 37 G x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m).
  Proof.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2.
    intros. eapply (pct_dispatch q lo S MB A len cap cur0 bs VOK _ fp 120); [exact MI| reflexivity| lia| exact RD| exact Hb2|].
    cbn [vjt_off Z.eqb Pos.eqb Z.add].
    eapply x_body; eassumption.
  Qed.
End VF3.
