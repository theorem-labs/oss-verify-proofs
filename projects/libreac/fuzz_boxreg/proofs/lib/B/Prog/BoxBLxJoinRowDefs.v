(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module paths and module names changed; 223 of its 269 lines of code are new or changed and 934 lines of the source are left out. *)
(* The phase JOIN of the walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput: the shared data of check_kept's row
   loop (0x80b44 .. 0x80c4c), used by BoxBLxJoinRow.v (rows, lx_join) and BoxBLxJoinRowBC.v (the name test and the
   loop's branch). Row j (s7 = 56 j, s8 = 56 renamed, s10 = 56 n, n = prev.n <= 5, so j <= 4) is cut at
   - LP_L 0x80b44 (BoxBLxJoin.v LI_L): the loop head;
   - LP_M 0x80c2c (LI_R LP_M): the three words and the MAC checked; s3 = r + 56 j, s9 = prev + 56 j;
   - LP_N 0x80c44 (LI_R LP_N): the name checked.
   The walk tactics of BoxBLxJoin.v are repeated here: an Ltac definition does not leave its Section. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h BoxBLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC45 YC85 BoxBLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Bytes Mem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxJoin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* Offsets in the listing: after the MAC checks (0x80c2c) and after the name check (0x80c44). *)
Definition LP_M : Z := 0xc80.
Definition LP_N : Z := 0xc98.

(* The seat of row j (rows 0 .. 4: j is a numeral): s7 = 56 j; the slots ~r (0x70) and ~prev (0x78) as atoms 48, 49;
   row j's base / nch / pinned words as atoms 50, 51, 52, the same chunk values in prev (frame region) and in r (a
   region of the registry block, atom 20): lkept_words. *)
Definition RA_fcs (j : Z) : list YP09.chunk :=
  [YP09.mkChunk (64 + 56 * j + 8) (CVal 4 (SOff 50 0)); YP09.mkChunk (64 + 56 * j + 12) (CVal 4 (SOff 51 0));
   YP09.mkChunk (64 + 56 * j + 20) (CVal 4 (SOff 52 0))].
Definition RA_blk (j : Z) : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 288 0 0
    [YP09.mkChunk (56 * j + 8) (CVal 4 (SOff 50 0)); YP09.mkChunk (56 * j + 12) (CVal 4 (SOff 51 0));
     YP09.mkChunk (56 * j + 20) (CVal 4 (SOff 52 0))].
(* The registry block's atom: 16-aligned, below the allocator's ceiling (the shadow token's span needs the bound). *)
Definition RA_G : facts := mkFacts (LX_AF ++ [(20%nat, mkAF 4096 0x7fffff800000 4)]) [] [].
Definition RA_SH : list shent := [mkSHE 20 0 288; mkSHE LA_F 64 352].
Definition RA_ov (j : Z) : list (bv 5 * sv) := ((23%bv : bv 5), SLit (56 * j)) :: LX_OVP.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

(* BoxBLxJoin.v's walk tactics (an Ltac definition does not leave its Section); the same text. *)
(* After a run with closed windows: the phase's facts extend to the run's memory (HKA : lx_keep .. m0 m). *)
Ltac lj_keep_run HKA :=
  lazymatch type of HKA with lx_keep ?cx ?fp ?W ?rs ?m0 ?m =>
  lazymatch goal with HFr0 : frame_of _ _ (mrestrict _ m) (mrestrict _ ?m') |- _ =>
    let H := fresh "HKA" in
    assert (H : lx_keep cx fp W rs m0 m')
      by (eapply lx_keep_trans; [exact HKA | apply lj_keep_eq; exact (lj_aview_ro _ _ _ _ _ HFr0 ltac:(vm_compute; reflexivity))]);
    clear HKA; rename H into HKA;
    repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end
  end end.
(* A register of the symbolic state, as the symbolic value it holds. *)
Ltac lj_reg HS r R :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R end.
(* A fact of the phase, from the cut's fact and the keep relation in the context. *)
Ltac lj_keepf0 L :=
  eapply L; try eassumption; try lia; try (left; reflexivity);
  try (unfold LSH_iter, LSH_entry; change (fs_frame_bytes LX_CID / 8) with 64; cbn [length app repeat]; lia).
Ltac lj_kf :=
  first [ solve [lj_keepf0 lx_saved_keep] | solve [lj_keepf0 lx_shadow_keep] | solve [lj_keepf0 lx_flag_keep]
        | solve [lj_keepf0 lx_slot_keep] | solve [lj_keepf0 lx_input_keep] | solve [lj_keepf0 lx_reg_keep]
        | solve [lj_keepf0 lx_prev_keep] | solve [lj_keepf0 lx_cur_keep] | solve [lj_keepf0 lx_slots_loop_keep] ].
(* lx_body at the landing state HS (registers from the symbolic state, the rest kept). *)
Ltac lj_land_body HS :=
  eapply lx_land; [eassumption | exact HS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf].
(* Close region i's window in the seat's state, and normalize the state. *)
Ltac lj_unwin_tac HS i :=
  let H := fresh "HSu" in
  pose proof (lj_unwin _ _ _ i _ HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)) as H;
  clear HS; rename H into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
(* An address the phase's facts speak about (Seat's lx_keep_at), from the bounds in the context. *)
Ltac lj_keep_at_tac :=
  unfold lx_keep_at;
  first [ left; lia | right; left; lia | right; right; left; change (fs_frame_bytes LX_CID) with 512; lia
        | right; right; right; left; change (fs_frame_bytes LX_CID / 8) with 64; lia
        | right; right; right; right; apply Exists_cons_hd; cbn [fst snd]; unfold LX_REG; lia ].
(* After a call that kept the phase's facts (HK : lx_keep ...): the regions idxs survive (their windows are closed). *)
Ltac lj_reseat HS HP W3 mem2 HK idxs :=
  let K := run_K_hi HS in
  let HS2 := fresh "HS2" in
  lazymatch type of HP with aregs_preserved _ ?regs2 =>
    jafter_call_keep_hi HS K regs2 (mrestrict (w_H W3) mem2) HP idxs HS2 end;
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in assert (HQ : Q);
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      (apply lj_rkept; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
       [ let a := fresh "a" in let Ha := fresh "Ha" in
         intros a Ha; rewrite ?YN3v.ew_havoc_old in Ha by lia;
         repeat match goal with Hu : bv_unsigned (ew ?Ex ?n) = _ |- _ =>
           lazymatch type of Ha with context [bv_unsigned (ew Ex n)] => rewrite Hu in Ha end end;
         apply HK; lj_keep_at_tac
       | lia ])
    | specialize (HS2 HQ); clear HQ ] end;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
(* After a call (havoc above K): the facts on the old atoms hold in the new environment (grant's restate). *)
Ltac lj_restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = v |- _ => fail
      | _ => let F' := fresh F in assert (F' : ew En n = v) by (rewrite OLD by lia; exact F); clear F; rename F' into F
      end
  | F : bv_unsigned (ew Eo ?n) = ?v |- _ =>
      lazymatch goal with
      | _ : bv_unsigned (ew En n) = v |- _ => fail
      | _ => let F' := fresh F in assert (F' : bv_unsigned (ew En n) = v) by (rewrite OLD by lia; exact F); clear F; rename F' into F
      end
  end end.
(* Name the environment after a call (havoc E K ws) and carry the old atoms' facts and lx_E into it. *)
Ltac lj_newenv HS E1 HE1 OLD :=
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
    remember (havoc Eo K ws) as E1 eqn:HE1 in HS;
    assert (OLD : forall q, (q < K)%nat -> ew E1 q = ew Eo q)
      by (let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq);
    let HEIn := fresh "HEI" in
    assert (HEIn : img_env VAL A_LIM E1)
      by (rewrite HE1; apply img_env_havoc_hi; [assumption | cbv; lia]);
    let HEn := fresh "HE" in
    lazymatch goal with HEo : lx_E ?cx ?fp Eo |- _ =>
      assert (HEn : lx_E cx fp E1)
        by (apply (lx_E_agree cx fp Eo E1 HEo); let n := fresh "n" in let Hn := fresh "Hn" in
            intros n Hn; apply OLD; unfold LA_EX in Hn; lia);
      clear HEo end;
    lj_restate OLD;
    repeat match goal with H : img_env _ _ Eo |- _ => clear H end
  end.
Variable B : asyms.
Variable MT : ameter_ops.

(* 0x80c2c and 0x80c44, row j of check_kept's loop in turn i: LI_L's facts at pc, and s3 = r + 56 j,
   s9 = prev + 56 j. *)
Definition LI_R (pc : Z) (i : nat) (j : Z) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab ren : Z) (bs bs' : list byte),
  lx_body cx fp pc W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 3 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT /\
  lblk B cx ly3 S3 r /\ lprev cx fp W3 ms3 bs /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  lreg W3 ms3 r bs' /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = fab /\ lkept bs bs' ren /\
  -1 <= ren < Boxreg.bx_n bs /\ 0 <= j < Boxreg.bx_n bs /\
  lcur cx W3 ms3 pos /\ lslots_loop cx fp W3 ms3 r fab /\ lslot cx W3 ms3 0x58 (Z.of_nat i) /\
  getr (ms_regs ms3) 19 = w64 (r + 56 * j) /\ getr (ms_regs ms3) 20 = w64 r /\
  getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\
  getr (ms_regs ms3) 23 = w64 (56 * j) /\ getr (ms_regs ms3) 24 = w64 (56 * (ren mod 2 ^ 32)) /\
  getr (ms_regs ms3) 25 = w64 (lF cx fp + 64 + 56 * j) /\
  getr (ms_regs ms3) 26 = w64 (56 * Boxreg.bx_n bs) /\ getr (ms_regs ms3) 27 = w64 fab.

(* A 6-byte operand of bcmp, as aj_bcmp_at needs it (BoxBLxJoin.v lj_bcmp_prev / lj_bcmp_reg / lj_bcmp_zero). *)
Definition lr_obj (cx : lxcx) (W3 : world SEGS) (regsT : bvmap 5 word) (memT : word -> option byte) (x : Z) : Prop :=
  src_ok SEGS W3 regsT memT x 6 /\ (forall a, x <= a < x + 6 -> ~ (lsp1 cx - 2 * ESTACK <= a < lsp1 cx)) /\
  0 <= x /\ x + 6 <= 2 ^ 63 /\ amem_range x 6 /\
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF x 6 /\ shadow_hull_vis (aview SEGS (w_H W3) memT) x 6.

Hypothesis HY : lx_hyps B MT.

(* bcmp (x, y, 6) at sp = sp1, in the phase's journal (YCbq.v aj_bcmp_at, lh_bcmp). *)
Lemma lr_bcmp : forall cx fp (W3 : world SEGS) ly3 S3 k (regsT : bvmap 5 word) memT mdT x y,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 memT mdT k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 6 ->
  spZ regsT = lsp1 cx -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regsT 1) ->
  lr_obj cx W3 regsT memT x -> lr_obj cx W3 regsT memT y ->
  SRr SEGS W3 (mkCfg (YK11.mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
         [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (getr regs2 10 = w64 0 <->
          forall i, 0 <= i < 6 -> aview SEGS (w_H W3) memT (x + i) = aview SEGS (w_H W3) memT (y + i)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx - 2 * ESTACK <= a < lsp1 cx) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a)).
Proof.
  intros cx fp W3 ly3 S3 k regsT memT mdT x y HB HJ H10 H11 H12 Hsp Hgp Htp Hra
    (Hxs & Hxw & Hx0 & Hx1 & Hxm & Hxr & Hxh) (Hys & Hyw & Hy0 & Hy1 & Hym & Hyr & Hyh).
  pose proof (lh_laws B MT HY) as LAWS. pose proof pa_segs_low as Hsegs.
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HspT : spZ regsT = lsp0 cx + (lsp1 cx - lsp0 cx)) by lia.
  eapply SRr_mono.
  { eapply (aj_bcmp_at SEGS B LAWS Hsegs _ (lh_bcmp B MT HY) W3 regsT memT LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx)
      (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 mdT k x y 6 (lsp1 cx - lsp0 cx) (getr regsT 1) HJ
      H10 H11 H12 ltac:(lia) Hx0 ltac:(lia) Hy0 ltac:(lia) HspT (lj_sub_mod16 _ _ Hsp32 Hsp16) ltac:(lia)
      ltac:(unfold LX_STK; lia) Hgp Htp eq_refl Hra Hxs Hys);
      replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia.
    - exact Hxw.
    - exact Hyw.
    - exact Hxm.
    - exact Hym.
    - exact Hxr.
    - intros _. exact Hxh.
    - exact Hyr.
    - intros _. exact Hyh. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & _).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split.
  - rewrite Hv. exact Hcmp.
  - replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in Hfr by lia. exact Hfr.
Qed.

(* What a call keeps (every byte outside its stack area below sp1) keeps the phase's facts. *)
Lemma lr_keep_stk : forall cx fp (W3 : world SEGS) (ms : machine_state) ly3 S3 md3 k r m m',
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx - 2 * ESTACK <= a < lsp1 cx) ->
     aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  lx_keep cx fp W3 [(r, LX_REG)] m m'.
Proof.
  intros cx fp W3 ms ly3 S3 md3 k r m m' HB HJ HFR HBLK HK a Ha.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof (lx_sh_range B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ HFR) as (HSH0 & HSH1).
  pose proof asan_consts as (C1 & _).
  pose proof HJ as (HAR & _).
  pose proof HB as (_ & _ & _ & HPN & _).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFd : lF cx fp / 8 <= 35184372088832) by (apply Z.div_le_upper_bound; lia).
  assert (HSHA : lSH cx fp + 64 < alloc_ceiling) by (rewrite HSHe; unfold SHADOW_OFF; lia).
  unfold lx_keep_at in Ha. change (fs_frame_bytes LX_CID / 8) with 64 in Ha.
  change (fs_frame_bytes LX_CID) with 512 in Ha.
  assert (HA : 0 <= a < alloc_ceiling \/ lsp1 cx <= a < 2 ^ 64).
  { destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]]; try lia.
    - destruct HPN as [[Hn0 Hp0] | (Hn & Hinp)]; [unfold lc_n in *; lia|].
      assert (HinL : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
        by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; left; exact Hinp).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinL) as (_ & Hp4096 & Hpceil & _).
      pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hrq]. lia.
    - apply Exists_cons in Ha as [Ha | Ha]; [|apply Exists_nil in Ha; contradiction]. cbn [fst snd] in Ha.
      assert (HrIn : In (r, LX_REG) (ablocks B ly3 S3))
        by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR HrIn) as (_ & Hr4096 & Hrceil & _).
      change (req_size LX_REG) with 288 in Hrceil. unfold LX_REG in Ha. lia. }
  apply HK; lia.
Qed.

(* The MAC test of row j (0x80c10 .. 0x80c28). bcmp (prev.mac, ZERO, 6) is not 0: prev's MAC is not zero6. *)
Lemma lr_mac_nz : forall cx fp (W3 : world SEGS) (ms : machine_state) bs j z,
  lprev cx fp W3 ms bs -> 0 <= j < 5 ->
  (forall i, 0 <= i < 6 -> aview SEGS (w_H W3) (ms_mem ms) (z + i) = Some 0) ->
  ~ (forall i, 0 <= i < 6 ->
       aview SEGS (w_H W3) (ms_mem ms) (lF cx fp + 64 + 56 * j + i) = aview SEGS (w_H W3) (ms_mem ms) (z + i)) ->
  Boxreg.bx_mac bs j <> Boxreg.zero6.
Proof.
  intros cx fp W3 ms bs j z HPV Hj HZ HNZ Hm0. apply HNZ. intros t Ht. unfold lprev, lview in HPV.
  rewrite HZ by exact Ht.
  replace (lF cx fp + 64 + 56 * j + t) with (lF cx fp + 64 + (56 * j + t)) by lia.
  rewrite (HPV (56 * j + t) ltac:(unfold LX_REG; lia)).
  rewrite (lj_mac_zero bs j t ltac:(lia) Ht Hm0). reflexivity.
Qed.

(* A MAC that is not zero6 stays (lkept): bcmp (prev.mac, r.mac, 6) sees equal bytes. *)
Lemma lr_mac_keep : forall cx fp (W3 : world SEGS) (ms : machine_state) r bs bs' ren j,
  lprev cx fp W3 ms bs -> lreg W3 ms r bs' -> lkept bs bs' ren -> 0 <= j < Boxreg.bx_n bs -> j < 5 ->
  Boxreg.bx_mac bs j <> Boxreg.zero6 ->
  forall i, 0 <= i < 6 ->
    aview SEGS (w_H W3) (ms_mem ms) (lF cx fp + 64 + 56 * j + i) = aview SEGS (w_H W3) (ms_mem ms) (r + 56 * j + i).
Proof.
  intros cx fp W3 ms r bs bs' ren j HPV HRG HKP Hj Hj5 Hnz i Hi.
  unfold lprev, lreg, lview in *.
  destruct (HKP j Hj) as (_ & _ & _ & [Hm0 | Hmeq] & _); [contradiction|].
  replace (lF cx fp + 64 + 56 * j + i) with (lF cx fp + 64 + (56 * j + i)) by lia.
  replace (r + 56 * j + i) with (r + (56 * j + i)) by lia.
  rewrite (HPV (56 * j + i) ltac:(unfold LX_REG; lia)), (HRG (56 * j + i) ltac:(unfold LX_REG; lia)).
  rewrite (lj_mac_eq bs bs' j i _ ltac:(lia) Hi Hmeq). reflexivity.
Qed.

(* The name test of row j (0x80c3c): a row that was not renamed keeps its name (lkept). *)
Lemma lr_name_same : forall bs bs' ren j, lkept bs bs' ren -> 0 <= j < Boxreg.bx_n bs -> j <> ren ->
  abfm_strn_eq (Z.to_nat 32) (lname bs j) (lname bs' j).
Proof.
  intros bs bs' ren j HKP Hj Hne. destruct (HKP j Hj) as (_ & _ & _ & _ & [-> | Hn]); [contradiction|].
  rewrite (lname_eq bs bs' j Hn). reflexivity.
Qed.

End a.
