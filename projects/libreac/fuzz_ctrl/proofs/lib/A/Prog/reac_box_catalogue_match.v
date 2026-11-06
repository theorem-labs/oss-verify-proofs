(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_model_block
  reac_box_catalogue_match_c reac_box_catalogue_match_lib.
Import ListNotations.
Open Scope Z_scope.
(* The store hook this file's proofs use: also transport rd_mono across a store. Text of lib/A/Prog/MemMono.v (a version not in this delivery; written on a working branch 8bac67328ab),
   whose redefinition is Local there; Local
   here too (a Theorem Labs lane 11:28Z). *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* reac_box_catalogue_match, image A (asan, entry 0x84498): reac_box_catalogue_match_holds (the contract of
   reac_box_catalogue_match_c.v) from the contracts of reac_ctrl_parse, reac_box_model_block, the bcmp wrapper and
   __asan_stack_malloc_2. The plain proof (lib/Prog/reac_box_catalogue_match.v) with the 192-byte class-2 side-stack
   frame of this build: the frame request (or the real-stack fallback probe), the frame magic words and their shadow
   bytes, the shadow check before each instrumented load (each passes from the addressable-range premises, so
   __asan_report_* is not reached), reac_ctrl_parse / reac_box_model_block / the bcmp wrapper at the frame buffers by
   their asan contracts, and the frame release. *)

(* Every range of fp_w [0;1;2] FS lies in the side stack [FS, FS + FS_SIZE) or is the shadow of a range there; a byte
   of application memory above the side stack is apart from all of them. *)
Lemma fpw3_out_hi : forall FS x, FS mod 4096 = 0 -> 0 < FS -> FS + FS_SIZE <= APPMEM_END ->
  FS + FS_SIZE <= x -> app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros FS x H4 HP HAE Hx Hap.
  cbn [fp_w flat_map fp_w1 app].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 14) with 16384. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096.
  change (2 ^ 15) with 32768. change (2 ^ 20) with 1048576.
  change (2 ^ 1) with 2. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
  repeat first
    [ exact I
    | split; [ apply acl_sh_out; [ exact Hap | unfold FS_SIZE in *; lia | unfold FS_SIZE, APPMEM_END in *; lia ] | ]
    | split; [ intros [? ?]; unfold FS_SIZE in *; lia | ] ].
Qed.


(* A point outside a footprint is apart from any single range of it. *)
Lemma out_in : forall W a b x, outside W x -> In (a, b) W -> ~ (a <= x < b).
Proof.
  induction W as [|[lo hi] W IH]; intros a b x H Hin; cbn in Hin; [contradiction|].
  destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; exact H1 | exact (IH a b x H2 Hin)].
Qed.

Lemma fpw3_in_frame : forall FS c, In c [0%nat; 1%nat; 2%nat] ->
  In (fs_frame FS c 0, fs_frame FS c (fs_M c)) (fp_w [0%nat; 1%nat; 2%nat] FS).
Proof.
  intros FS c Hc. apply in_flat_map. exists c. split; [exact Hc|]. cbn [fp_w1 In]. right; right; left; reflexivity.
Qed.

(* A byte of application memory apart from the side-stack bytes has its shadow byte apart from them too. *)
Lemma fpw3_out_sh : forall FS x, FS mod 4096 = 0 -> 0 < FS -> FS + FS_SIZE <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) -> app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  outside (fp_w [0%nat; 1%nat; 2%nat] FS) (shadow_addr x).
Proof.
  intros FS x H4 HP HAE HAPP Hap Ho.
  pose proof (rt_app_shadow x Hap) as Hs.
  assert (NA : forall a b, (forall z, a <= z < b -> app_mem z) -> ~ (a <= shadow_addr x < b)).
  { intros a b Hab Hin. exact (acl_app_not_shadow _ (Hab _ Hin) Hs). }
  pose proof (out_in _ _ _ _ Ho (fpw3_in_frame FS 0 ltac:(cbn; tauto))) as HF0.
  pose proof (out_in _ _ _ _ Ho (fpw3_in_frame FS 1 ltac:(cbn; tauto))) as HF1.
  pose proof (out_in _ _ _ _ Ho (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as HF2.
  clear Ho.
  cbn [fp_w flat_map fp_w1 app].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
  change (2 ^ 14) with 16384 in *. change (2 ^ 13) with 8192 in *. change (2 ^ 12) with 4096 in *.
  change (2 ^ 15) with 32768 in *. change (2 ^ 20) with 1048576 in *.
  change (2 ^ 1) with 2 in *. change (2 ^ 2) with 4 in *. change (2 ^ 0) with 1 in *.
  repeat first
    [ exact I
    | split; [ apply NA; intros z Hz; apply HAPP; unfold FS_SIZE in *; lia | ]
    | split; [ apply acl_win_sh; [ unfold FS_SIZE in *; Z.div_mod_to_equations; lia
                                 | first [ exact HF0 | exact HF1 | exact HF2 ] ] | ] ].
Qed.

(* Three class-footprint lemmas this proof uses, file-local: the text of the image-A RcAsanFPLib.v this proof was written
   against (a working branch 82b481fc405, lines 413-439); the RcAsanFPLib.v of this tree does not have them. *)
(* fp_w for a single class is a sublist of fp_w for a class list that contains it. *)
Lemma fp_w_incl : forall c cs FS, In c cs -> incl (fp_w [c] FS) (fp_w cs FS).
Proof.
  intros c cs FS Hin d Hd. unfold fp_w in *. cbn [flat_map] in Hd. rewrite app_nil_r in Hd.
  apply in_flat_map. exists c. split; [exact Hin | exact Hd].
Qed.

(* fp_dj to a sublist of the apart list. *)
Lemma fp_dj_incl : forall D L L', incl L' L -> fp_dj D L -> fp_dj D L'.
Proof.
  intros D L L' Hi H. unfold fp_dj in *. eapply Forall_impl; [|exact H].
  intros d Hd. cbn beta in Hd. apply Forall_forall. intros x Hx. rewrite Forall_forall in Hd. apply Hd, Hi, Hx.
Qed.

(* fp for a single class c of a class list cs that contains it, at the same window. *)
Lemma fp_single : forall c cs m TP FS lo hi W D, In c cs ->
  fp cs m TP FS lo hi W D -> fp [c] m TP FS lo hi W D.
Proof.
  intros c cs m TP FS lo hi W D Hin
    (DT & TS & C & T & DB & k & HT & B1 & FSP & B2 & B3 & HCL & HFS & HAPP & HWd & HDd).
  exists DT, TS, C, T, DB, k. split; [exact HT|]. split; [exact B1|]. split; [exact FSP|].
  split; [exact B2|]. split; [exact B3|].
  split; [constructor; [rewrite Forall_forall in HCL; apply HCL; exact Hin | constructor]|].
  split; [exact HFS|]. split; [exact HAPP|]. split; [exact HWd|].
  apply (fp_dj_incl D (fp_w cs FS)); [apply fp_w_incl; exact Hin | exact HDd].
Qed.

Section Match.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis HPC : reac_ctrl_parse_contract.
Hypothesis HMB : reac_box_model_block_contract.
Hypothesis HBC : bcmp_wrap_contract.
Hypothesis HSM : asan_stack_malloc_2_contract.
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hwin : forall a, S - 9136 <= a < S -> seg_rom rsegs (wa a) = None.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HF : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - 9136 \/ S <= f).
Hypothesis HT : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SR : shadow_rw m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis AFU : 50 <= len -> addressable m f 50 /\ app_mem (f + 50).
Hypothesis AT : addressable m CM_T 3256.
Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HGOT : bytes_at rsegs m GOT_CF (le8 (wa CF)).
Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).
Hypothesis TLS0 : reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - 9136) S.

Definition aWf : list ivl := [(S - 9136, S)].
Definition aDf : list ivl := if len <? 50 then [] else [(f, f + 50)].
Definition aXs : list ivl := fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - 9136), shadow_addr S)].
Definition aWc : list ivl := (S - 9136, S) :: aXs.

Definition aTL (mc : word -> option byte) : Prop :=
  forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
    fp_dj (fp_tls (bv_unsigned tp) DT TS C T DB kk) aXs.

Definition aJa (mc : word -> option byte) : Prop :=
  asan_cells mc /\ shadow_rw mc /\ addressable mc (S - 9136) 9136 /\
  fp [0%nat; 1%nat; 2%nat] mc (bv_unsigned tp) FS (S - 9136) S aWf aDf /\ aTL mc.

(* The side stack's place and the data ranges apart from the class-0/1/2 side-stack bytes (fp in m). *)
Lemma acl_fs : 0 < FS /\ FS mod 4096 = 0 /\ ASAN_GT <= FS /\ FS + FS_SIZE <= S - 9136 /\
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) /\ fp_dj aDf (fp_w [0%nat; 1%nat; 2%nat] FS).
Proof.
  destruct FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & _) & _ & _ & _ & HFS & HAPP & _ & HDd).
  unfold reac_box_catalogue_match_D in HDd. fold aDf in HDd.
  repeat split; assumption.
Qed.

Lemma acl_out_fpw_d : forall a b x, In (a, b) aDf -> a <= x < b -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros a b x Hin Hx. destruct acl_fs as (_ & _ & _ & _ & _ & DJ). exact (fl_dj_out_r _ _ a b x DJ Hin Hx).
Qed.

Lemma acl_out_fpw_hi : forall x, FS + FS_SIZE <= x -> app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros x Hx Hap. destruct acl_fs as (P1 & P2 & P3 & P4 & P5 & _).
  apply fpw3_out_hi; [exact P2 | exact P1 | clear -P4 HAE; lia | clear -Hx; lia | exact Hap].
Qed.

Lemma acl_out_fpw_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  outside (fp_w [0%nat; 1%nat; 2%nat] FS) (shadow_addr x).
Proof.
  intros x Hap Ho. destruct acl_fs as (P1 & P2 & P3 & P4 & P5 & _).
  apply fpw3_out_sh; [exact P2 | exact P1 | clear -P4 HAE; lia | exact P5 | exact Hap | exact Ho].
Qed.

Lemma acl_out_Xs_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  (x < S - 9136 \/ S <= x) -> outside aXs (shadow_addr x).
Proof.
  intros x Hap Ho Hx. unfold aXs. apply fl_out_app; [exact (acl_out_fpw_sh x Hap Ho)|].
  cbn [outside]. split; [|exact I].
  apply acl_win_sh; [apply acl_S_mod8; [exact S16 | reflexivity] | clear -Hx; lia].
Qed.

Lemma acl_out_Wc_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  (x < S - 9136 \/ S <= x) -> outside aWc (shadow_addr x).
Proof.
  intros x Hap Ho Hx. pose proof (rt_app_shadow x Hap) as Hs. unfold aWc. cbn [outside].
  split; [clear -Hs HHM; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia|].
  exact (acl_out_Xs_sh x Hap Ho Hx).
Qed.

Lemma acl_out_Wc : forall x, app_mem x -> (x < S - 9136 \/ S <= x) ->
  outside (fp_w [0%nat; 1%nat; 2%nat] FS) x -> outside aWc x.
Proof.
  intros x Hap H3 H4. unfold aWc, aXs. cbn [outside].
  split; [clear -H3; lia|].
  apply fl_out_app; [exact H4|]. cbn [outside]. split; [|exact I].
  apply acl_sh_out; [exact Hap | clear -HK; lia | exact HAE].
Qed.

(* The runtime state survives writes inside the window [S - 9136, S). *)
Lemma ja_win : forall W' m1 m2, aJa m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(S - 9136, S)] ->
  aJa m2.
Proof.
  intros W' m1 m2 (AC1 & SW & AW1 & FP & TL1) MU WM Hs.
  assert (SHo : forall x, in_shadow x -> outside W' x)
    by (intros x Hx; exact (fl_shadow_out W' (S - 9136) S x Hs HHM Hx)).
  unfold aWf in FP.
  split; [|split; [|split; [|split]]].
  - apply (fl_asan_cells W' m1 m2 AC1 MU). intros x Hx. apply (fl_out_lo W' (S - 9136) S x Hs). left.
    clear -Hx HHM. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
  - exact (fl_shadow_rw W' m1 m2 SW MU WM SHo).
  - exact (fl_addressable W' m1 m2 _ _ AW1 MU SHo).
  - exact (fl_fp _ m1 m2 (bv_unsigned tp) FS (S - 9136) S _ aDf W' FP MU WM Hs).
  - exact (fl_tls _ m1 m2 (bv_unsigned tp) FS (S - 9136) S _ aDf W' aXs FP MU Hs TL1).
Qed.

(* The shadow byte of fr + 8 i is i above the shadow byte of fr. *)
Lemma cm_sh_add8 : forall fr i, fr mod 8 = 0 -> shadow_addr (fr + 8 * i) = shadow_addr fr + i.
Proof. intros fr i Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The aligned frame pointer: sp after andi sp, (sp - 128), -32. *)
Definition CA : Z := (S - 128) / 32 * 32.

Lemma CA_facts : CA mod 32 = 0 /\ S - 160 <= CA <= S - 128.
Proof. unfold CA. Z.div_mod_to_equations. lia. Qed.

(* The 192-byte class-2 frame: real (fr = CA - 192, body sp = CA - 192) or a side-stack frame fs_frame FS 2 jj
   (body sp = CA). *)
Definition cmFK (fr sp2 jj nn : Z) : Prop :=
  (fr = CA - 192 /\ sp2 = CA - 192 /\ jj = 0 /\ nn = 0) \/
  (0 <= jj < fs_M 2 /\ fr = fs_frame FS 2 jj /\ sp2 = CA /\ nn = 1).

(* Each frame is 8-aligned, below the window top, writable and application memory, with writable shadow bytes. *)
Lemma fk_facts : forall fr sp2 jj nn, cmFK fr sp2 jj nn ->
  fr mod 8 = 0 /\ 0 < fr /\ fr + 192 <= CA /\
  (forall i, 0 <= i < 192 -> wview rsegs m (wa (fr + i)) <> None) /\
  (forall i, 0 <= i < 192 -> app_mem (fr + i)) /\
  (forall i, 0 <= i < 24 -> wview rsegs m (wa (fr / 8 + ASAN_K + i)) <> None) /\
  (sp2 = CA \/ sp2 = CA - 192).
Proof.
  intros fr sp2 jj nn HFK.
  pose proof CA_facts as (CAm & CAlo & CAhi).
  destruct FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFS & _).
  unfold FS_SIZE in HFS, P4. pose proof P5 as (_ & _ & P5h). unfold FS_SIZE in P5h.
  pose proof ST as (_ & _ & STh). destruct AW as (_ & _ & _ & AWh).
  assert (BASE : fr mod 8 = 0 /\ 0 < fr /\ fr + 192 <= CA /\
    (forall i, 0 <= i < 192 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 192 -> app_mem (fr + i)) /\ (sp2 = CA \/ sp2 = CA - 192)).
  { destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr sp2.
    - split; [unfold CA; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      split; [intros i Hi; apply (proj1 (STh (CA - 192 + i) ltac:(lia)))|].
      split; [|right; reflexivity].
      intros i Hi. replace (CA - 192 + i) with (S - 9136 + (CA - 192 + i - (S - 9136))) by lia.
      exact (proj1 (AWh (CA - 192 + i - (S - 9136)) ltac:(lia))).
    - assert (M8 : fs_frame FS 2 jj mod 8 = 0).
      { unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. Z.div_mod_to_equations; lia. }
      assert (LO : FS + 36864 <= fs_frame FS 2 jj).
      { unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
      assert (HI : fs_frame FS 2 jj + 256 <= FS + FS_SIZE).
      { unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj.
        unfold FS_SIZE. lia. }
      unfold FS_SIZE in HI.
      split; [exact M8|]. split; [lia|]. split; [lia|].
      split; [intros i Hi; exact (proj1 (P5h (fs_frame FS 2 jj + i) ltac:(lia)))|].
      split; [|left; reflexivity].
      intros i Hi. apply P4. lia. }
  destruct BASE as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
  split; [|exact B6].
  intros i Hi. pose proof (B5 (8 * i) ltac:(lia)) as Ap.
  pose proof (rt_app_shadow (fr + 8 * i) Ap) as Sh.
  replace (fr / 8 + ASAN_K + i) with (shadow_addr (fr + 8 * i))
    by (rewrite (cm_sh_add8 fr i B1); unfold shadow_addr; lia).
  exact (proj1 (SR _ Sh)).
Qed.

(* ============================ (a) entry ============================ *)

(* The 12 callee-saved registers stored at [S-96, S): s10..ra ascending. *)
Definition cmSAVES : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* A byte stays addressable under writes apart from its shadow byte. *)
Lemma cm_ab_keep : forall W mm mm' x, addr_byte mm x -> munch W mm mm' -> outside W (shadow_addr x) ->
  addr_byte mm' x.
Proof.
  intros W mm mm' x AB MU Ho.
  pose proof (proj1 AB) as Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap.
  assert (AD : addressable mm x 1).
  { split; [clear -Hap; lia|]. split; [clear; lia|]. split; [unfold APPMEM_END; clear -Hap; lia|].
    intros i Hi. replace (x + i) with x by (clear -Hi; lia). exact AB. }
  destruct (addr_munch W mm mm' x 1 AD MU
              ltac:(intros i Hi; replace (x + i) with x by (clear -Hi; lia); exact Ho)) as (_ & _ & _ & ADb).
  pose proof (ADb 0 ltac:(clear; lia)) as AB'. replace (x + 0) with x in AB' by (clear; lia). exact AB'.
Qed.

(* The window's bytes outside the frame are addressable: the frame's own 24 shadow bytes carry the frame magic
   until the exit sets them back, and no other shadow byte of the window changes. *)
Definition cmAWX (fr : Z) (mc : word -> option byte) : Prop :=
  forall x, S - 9136 <= x < S -> ~ (fr <= x < fr + 192) -> addr_byte mc x.

(* The state carried from the entry to the gate (pc 0x845dc): the geometry, the write relation, the runtime cells,
   the whole side-stack state (fp [0;1;2]), the callee window addressable, the saves, and (side path) the flag
   pointer word the epilogue reads. *)
Definition cmInv (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  cmFK fr sp2 jj nn /\
  munch aWc m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
  asan_cells mc /\ shadow_rw mc /\
  fp [0%nat; 1%nat; 2%nat] mc (bv_unsigned tp) FS (S - 9136) S aWf aDf /\ aTL mc /\
  addressable mc (sp2 - 8800) 8800 /\ cmAWX fr mc /\
  rw_cells rsegs mc (S - 96) cmSAVES /\
  (nn = 1 -> bytes_at rsegs mc (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj)))).

(* The register state at the gate (0x845dc): s0 = S, s1 = CA, s2 = frame (0 real / fr side), s3 = f, s4 = len,
   s5 = ASAN_K, s6 = shadow_addr fr, s7 = fr, a2 = 50. *)
Definition cmKB (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    cmInv fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).
Lemma cm_CA_lo : S - 144 <= CA <= S - 128.
Proof. unfold CA. pose proof S16 as H16. Z.div_mod_to_equations. lia. Qed.

Definition cmHF (fr : Z) : list ivl :=
  [(CA + 24, CA + 32); (fr, fr + 24); (shadow_addr fr, shadow_addr fr + 24)].

Lemma cm_out_app : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I|exact H]|].
  destruct H as (H1 & H2). destruct (IH B x H2) as (HA & HB). split; [split; [exact H1|exact HA]|exact HB].
Qed.

Lemma fpw3_in_shadow : forall FS0 c, In c [0%nat; 1%nat; 2%nat] ->
  In (shadow_addr (fs_frame FS0 c 0), shadow_addr (fs_frame FS0 c (fs_M c))) (fp_w [0%nat; 1%nat; 2%nat] FS0).
Proof.
  intros FS0 c Hc. apply in_flat_map. exists c. split; [exact Hc|]. cbn [fp_w1 In]. right; right; right; left; reflexivity.
Qed.

Lemma cm_fr_bounds : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> ASAN_GT <= fr /\ fr + 256 <= S.
Proof.
  intros fr sp2 jj nn FK. pose proof cm_CA_lo as (CAlo2 & CAhi2). pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj). unfold FS_SIZE in FShi.
  destruct FK as [(Efr & Esp & Ej & En) | (Hj & Efr & Esp & En)]; subst fr.
  - split; unfold ASAN_GT; lia.
  - unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
    change (2 ^ 20) with 1048576 in *. change (2 ^ (14 - 2)) with 4096 in Hj.
    unfold ASAN_GT in FSgt. split; unfold ASAN_GT; lia.
Qed.

Lemma cm_sub : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> sub_fp (cmHF fr) aWc.
Proof.
  intros fr sp2 jj nn FK x Hout.
  pose proof cm_CA_lo as (CAlo2 & CAhi2). pose proof CA_facts as (CA32 & CAlo & CAhi).
  unfold aWc in Hout. cbn [outside] in Hout. destruct Hout as (Hw & Hxs).
  unfold aXs in Hxs. apply cm_out_app in Hxs. destruct Hxs as (Hfpw & Hws).
  cbn [outside] in Hws. destruct Hws as (Hws & _).
  unfold cmHF. cbn [outside]. split; [|split; [|split; [|exact I]]].
  - clear -Hw CAlo2 CAhi2. lia.
  - destruct FK as [(Efr & _ & _ & _) | (Hj & Efr & _ & _)]; subst fr.
    + clear -Hw CAlo2 CAhi2. lia.
    + pose proof (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as HFin.
      unfold fs_frame, fs_B, fs_M in HFin, Hj |- *. cbn [Z.of_nat] in HFin, Hj |- *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ (14 - 2)) with 4096 in *. lia.
  - destruct FK as [(Efr & _ & _ & _) | (Hj & Efr & _ & _)]; subst fr.
    + assert (GE : shadow_addr (S - 9136) <= shadow_addr (CA - 192)) by (apply acl_sh_ge; lia).
      assert (LE : shadow_addr (CA - 192) + 24 <= shadow_addr S)
        by (unfold shadow_addr; Z.div_mod_to_equations; lia).
      clear -Hws GE LE. lia.
    + pose proof (out_in _ _ _ _ Hfpw (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as HFin.
      assert (GE : shadow_addr (fs_frame FS 2 0) <= shadow_addr (fs_frame FS 2 jj)).
      { apply acl_sh_ge. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. lia. }
      assert (LE : shadow_addr (fs_frame FS 2 jj) + 24 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
      { unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ (14 - 2)) with 4096 in Hj.
        Z.div_mod_to_equations; lia. }
      clear -HFin GE LE. lia.
Qed.

(* A shadow byte is apart from any range made of application bytes. *)
Lemma sh_out_app : forall s a b, in_shadow s -> (forall z, a <= z < b -> app_mem z) -> ~ (a <= s < b).
Proof. intros s a b Hs Hab [H1 H2]. exact (acl_app_not_shadow s (Hab s ltac:(lia)) Hs). Qed.

(* An application byte apart from the header's two application ranges (the sd s7 slot at CA+24 and the three header
   words at fr) is apart from the whole header footprint cmHF (its shadow range is in shadow memory). *)
Lemma cmHF_out_pt : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> app_mem x ->
  ~ (CA + 24 <= x < CA + 32) -> ~ (fr <= x < fr + 24) -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hap H1 H2.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & _ & _ & _ & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  unfold cmHF. cbn [outside]. split; [exact H1|]. split; [exact H2|]. split; [|exact I].
  pose proof (acl_sh_out x fr (fr + 8 * 24) Hap ltac:(lia) ltac:(lia)) as Ho.
  rewrite (cm_sh_add8 fr 24 FR8) in Ho. exact Ho.
Qed.

(* A byte of the side stack's header [FS, FS + 36864) is apart from the header footprint cmHF. *)
Lemma cmHF_out_side : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> FS <= x < FS + 36864 -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
  apply (cmHF_out_pt fr sp2 jj nn x FK Hap).
  - lia.
  - destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; subst fr.
    + lia.
    + unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia.
Qed.

(* A byte of the runtime's cells [RT_LO, RT_HI) is apart from the header footprint cmHF. *)
Lemma cmHF_out_rt : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> RT_LO <= x < RT_HI -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  unfold RT_LO, RT_HI in Hx.
  assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
  apply (cmHF_out_pt fr sp2 jj nn x FK Hap).
  - lia.
  - unfold ASAN_GT in FRgt. lia.
Qed.

(* The 12 saved registers [S - 96, S) are apart from the header footprint cmHF. *)
Lemma cmHF_out_saves : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> S - 96 <= x < S -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  assert (Hap : app_mem x) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
  apply (cmHF_out_pt fr sp2 jj nn x FK Hap).
  - lia.
  - destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; subst fr.
    + lia.
    + unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat] in Hj |- *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hj. lia.
Qed.

(* The epilogue's flag-pointer word [fr + 248, fr + 256) (side path) is apart from the header footprint cmHF. *)
Lemma cmHF_out_flag : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> nn = 1 -> fr + 248 <= x < fr + 256 ->
  outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Enn Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof FK as FKc.
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst nn. discriminate Enn.
  - assert (FRlo : FS + 36864 <= fr).
    { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
    assert (FRhi2 : fr + 256 <= FS + 11571200).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
    assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
    apply (cmHF_out_pt fr sp2 jj nn x FKc Hap).
    + lia.
    + lia.
Qed.

(* The shadow byte of a byte of the callee window [sp2 - 8800, sp2) is apart from the header footprint cmHF. *)
Lemma cmHF_sh_body : forall fr sp2 jj nn y, cmFK fr sp2 jj nn -> app_mem y -> sp2 - 8800 <= y < sp2 ->
  outside (cmHF fr) (shadow_addr y).
Proof.
  intros fr sp2 jj nn y FK Hap Hy.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & _ & _ & FAPP & _ & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof (rt_app_shadow y Hap) as Hsh.
  unfold cmHF. cbn [outside]. split; [|split; [|split; [|exact I]]].
  - apply (sh_out_app (shadow_addr y) (CA + 24) (CA + 32) Hsh).
    intros z Hz. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply (sh_out_app (shadow_addr y) fr (fr + 24) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by lia. apply FAPP. lia.
  - destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr sp2.
    + pose proof (acl_win_sh y (CA - 192) (CA - 192 + 8 * 24) FR8 ltac:(lia)) as Ho.
      rewrite (cm_sh_add8 (CA - 192) 24 FR8) in Ho. exact Ho.
    + assert (LEf : fs_frame FS 2 jj + 8 * 24 <= y).
      { unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat] in Hj |- *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
      pose proof (acl_win_sh y (fs_frame FS 2 jj) (fs_frame FS 2 jj + 8 * 24) FR8 ltac:(lia)) as Ho.
      rewrite (cm_sh_add8 (fs_frame FS 2 jj) 24 FR8) in Ho. exact Ho.
Qed.

(* The shadow byte of a window byte outside the frame is apart from the header footprint cmHF. *)
Lemma cmHF_sh_win : forall fr sp2 jj nn y, cmFK fr sp2 jj nn -> S - 9136 <= y < S -> ~ (fr <= y < fr + 192) ->
  outside (cmHF fr) (shadow_addr y).
Proof.
  intros fr sp2 jj nn y FK Hy Hyf.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & _ & _ & FAPP & _ & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia).
  pose proof (rt_app_shadow y Hap) as Hsh.
  unfold cmHF. cbn [outside]. split; [|split; [|split; [|exact I]]].
  - apply (sh_out_app (shadow_addr y) (CA + 24) (CA + 32) Hsh).
    intros z Hz. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply (sh_out_app (shadow_addr y) fr (fr + 24) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by lia. apply FAPP. lia.
  - pose proof (acl_win_sh y fr (fr + 8 * 24) FR8 ltac:(lia)) as Ho.
    rewrite (cm_sh_add8 fr 24 FR8) in Ho. exact Ho.
Qed.

(* The invariant survives the header run: writes land only in cmHF, which is inside the caller footprint aWc
   (cm_sub), and the side stack's class bytes fp_w [0;1;2] and the window shadow (fl_fp_free). *)
Lemma cm_inv_step : forall fr sp2 jj nn mc mc',
  cmInv fr sp2 jj nn mc ->
  munch (cmHF fr) mc mc' -> wmono rsegs mc mc' -> rd_mono mc mc' -> mem_inv rsegs mc' ->
  cmInv fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' INV MU WM RM MI'.
  destruct INV as (FK & MUmc & WMmc & RMmc & MImc & ACmc & SRmc & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_sub fr sp2 jj nn FK) as SUB.
  pose proof FPg as FPpack.
  destruct FPg as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTPle & HPl & H88 & H96 & HCL & HFSlo & HApphi & HWd & HDd).
  destruct HPl as (HP1 & HP2 & HP3 & HP4 & HPstk).
  split; [exact FK|].
  split; [exact (munch_trans aWc m mc mc' MUmc (munch_weaken (cmHF fr) aWc mc mc' SUB MU))|].
  split; [exact (wmono_trans rsegs m mc mc' WMmc WM)|].
  split; [exact (rd_mono_trans m mc mc' RMmc RM)|].
  split; [exact MI'|].
  split; [exact (fl_asan_cells (cmHF fr) mc mc' ACmc MU (fun x Hx => cmHF_out_rt fr sp2 jj nn x FK Hx))|].
  split; [exact (shadow_rw_mono mc mc' SRmc WM RM)|].
  split.
  { apply (fl_fp_free [0%nat; 1%nat; 2%nat] mc mc' (bv_unsigned tp) FS (S - 9136) S aWf aDf (cmHF fr) FPpack TLg MU WM).
    - unfold aWf, aWc, aXs. cbn [app]. exact SUB.
    - intros x Hx. apply (cmHF_out_side fr sp2 jj nn x FK). lia.
    - intros x Hx. right. apply RM. exact (rd_of_stk mc FS (FS + FS_SIZE) HPstk x Hx).
    - intros c Hc.
      pose proof (proj1 (Forall_forall _ _) HCL c Hc) as (Hc6 & h & flags & HH & HFf & HLn & HF01).
      split.
      + exists h. apply (fl_bytes (cmHF fr) mc mc' (fs_hint FS c) (le8 h) HH MU).
        intros x Hx. rewrite length_le8 in Hx. apply (cmHF_out_side fr sp2 jj nn x FK).
        unfold fs_hint in Hx. lia.
      + exists flags. split; [|split; [exact HLn | exact HF01]].
        apply (fl_bytes (cmHF fr) mc mc' (fs_flag FS c 0) flags HFf MU).
        intros x Hx. rewrite HLn in Hx. apply (cmHF_out_side fr sp2 jj nn x FK).
        unfold fs_flag, fs_M in Hx. destruct Hc as [E | [E | [E | []]]]; subst c; cbn [Z.of_nat] in Hx.
        * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 0)) with 32768 in Hx.
          change (2 ^ (14 - 0)) with 16384 in Hx. lia.
        * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 1)) with 16384 in Hx.
          change (2 ^ (14 - 1)) with 8192 in Hx. lia.
        * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 2)) with 8192 in Hx.
          change (2 ^ (14 - 2)) with 4096 in Hx. lia. }
  split.
  { intros DT TS C T DB kk HTcells'.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside (cmHF fr) x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUB. unfold aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLg DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same mc mc' (cmHF fr) (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells' MU Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLg DT TS C T DB kk HT0). }
  split.
  { apply (addr_munch (cmHF fr) mc mc' (sp2 - 8800) 8800 ADg MU).
    intros i Hi. apply (cmHF_sh_body fr sp2 jj nn (sp2 - 8800 + i) FK).
    - destruct ADg as (_ & _ & _ & ADbytes). exact (proj1 (ADbytes i Hi)).
    - lia. }
  split.
  { intros x Hx Hxf.
    exact (cm_ab_keep (cmHF fr) mc mc' x (AWXg x Hx Hxf) MU (cmHF_sh_win fr sp2 jj nn x FK Hx Hxf)). }
  split.
  { apply (acl_rw (cmHF fr) mc mc' (S - 96) cmSAVES SVg MU WM).
    intros x Hx. apply (cmHF_out_saves fr sp2 jj nn x FK).
    unfold cmSAVES in Hx. cbn [cells_size csize] in Hx. lia. }
  intros Enn.
  apply (fl_bytes (cmHF fr) mc mc' (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) (FLg Enn) MU).
  intros x Hx. rewrite length_le8 in Hx. apply (cmHF_out_flag fr sp2 jj nn x FK Enn). lia.
Qed.

(* The ASan shadow-check tactics this proof uses (chk_core with pre_sr / no_extra), file-local. The text is that of the
   longer image-A reac_box_model_block.v (blob 0dcbcb8154d, lines 313-351), which this proof was written against; the
   reac_box_model_block.v of this tree (after the MemMono split) does not define them. *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac no_extra X := idtac.

Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs m (wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs m (wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs m (wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.

Ltac cm_wst a n :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cm_wv | eassumption
            | try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.

(* The header run from 0x84538 to the gate at 0x845dc: the sd s7 at CA+24, the three header words at fr, fr+8, fr+16,
   and the 24 shadow bytes at shadow_addr fr + 0..23; it reaches the gate in the cmKB register state and rebuilds the
   invariant at the written memory (cm_inv_step), then hands control to the gate (eapply K). *)
Lemma cm_header : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 : word),
  cmKB Q -> cmInv fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84538) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 K INV.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  assert (cmSTW : forall a, S - 9136 <= a < S -> wview rsegs m (wa a) <> None)
    by (intros a Ha; exact (stk_wv m _ _ _ ST Ha)).
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold cmHF, shadow_addr in MUh.
  cm_wst (CA + 24) 8%nat. step. store_done.
  do 3 step.
  step. rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
  do 6 step.
  cm_wst fr 8%nat. step. store_done.
  cm_wst (fr + 8) 8%nat. step. store_done.
  cm_wst (fr + 16) 8%nat. step. store_done.
  step. step.
  assert (SHlo : 0 <= fr / 8 + ASAN_K).
  { assert (0 <= fr / 8) by (apply Z.div_pos; lia). unfold ASAN_K; lia. }
  assert (SHhi : fr / 8 + ASAN_K + 24 <= 2 ^ 64).
  { unfold ASAN_K. Z.div_mod_to_equations. lia. }
  cm_wst (fr / 8 + ASAN_K) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 1) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 2) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 3) 1%nat. step. store_done.
  step.
  cm_wst (fr / 8 + ASAN_K + 4) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 5) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 6) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 7) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 8) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 9) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 10) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 11) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 12) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 13) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 14) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 15) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 20) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 21) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 22) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 23) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 16) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 17) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 18) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 19) 1%nat. step. store_done.
  eapply K.
  eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

Lemma cm_forall_firstn : forall (A : Type) (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; cbn; [constructor|].
  destruct l as [|a l]; [constructor|]. inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma cm_forall_skipn : forall (A : Type) (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; cbn; [exact H|].
  destruct l as [|a l]; [constructor|]. inversion H; subst. apply IH; assumption.
Qed.

Lemma fpw3_in_hint : forall FS0 c, In c [0%nat; 1%nat; 2%nat] ->
  In (fs_hint FS0 c, fs_hint FS0 c + 8) (fp_w [0%nat; 1%nat; 2%nat] FS0).
Proof.
  intros FS0 c Hc. apply in_flat_map. exists c. split; [exact Hc|]. cbn [fp_w1 In]. left; reflexivity.
Qed.

Lemma fpw3_in_flag : forall FS0 c, In c [0%nat; 1%nat; 2%nat] ->
  In (fs_flag FS0 c 0, fs_flag FS0 c 0 + fs_M c) (fp_w [0%nat; 1%nat; 2%nat] FS0).
Proof.
  intros FS0 c Hc. apply in_flat_map. exists c. split; [exact Hc|]. cbn [fp_w1 In]. right; left; reflexivity.
Qed.

(* A byte of the runtime's cells [RT_LO, RT_HI) is apart from the caller footprint aWc. *)
Lemma acl_rt_out_Wc : forall x, RT_LO <= x < RT_HI -> outside aWc x.
Proof.
  intros x Hx. unfold RT_LO, RT_HI in Hx.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
  apply acl_out_Wc; [exact Hap | left; lia | ].
  cbn [fp_w flat_map fp_w1 app].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 14) with 16384. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096.
  change (2 ^ 15) with 32768. change (2 ^ 20) with 1048576.
  change (2 ^ 1) with 2. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
  repeat first
    [ exact I
    | split; [ apply acl_sh_out; [ exact Hap | unfold FS_SIZE in *; lia | unfold FS_SIZE, APPMEM_END in *; lia ] | ]
    | split; [ intros [? ?]; unfold FS_SIZE in *; lia | ] ].
Qed.

(* The side stack's header word range [FS + 80, FS + 104) is apart from the caller footprint aWc. *)
Lemma acl_hdr_out_Wc : forall x, FS + 80 <= x < FS + 104 -> outside aWc x.
Proof.
  intros x Hx.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
  apply acl_out_Wc; [exact Hap | left; lia | ].
  cbn [fp_w flat_map fp_w1 app].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 14) with 16384. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096.
  change (2 ^ 15) with 32768. change (2 ^ 20) with 1048576.
  change (2 ^ 1) with 2. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
  repeat first
    [ exact I
    | split; [ apply acl_sh_out; [ exact Hap | unfold FS_SIZE in *; lia | unfold FS_SIZE, APPMEM_END in *; lia ] | ]
    | split; [ intros [? ?]; unfold FS_SIZE in *; lia | ] ].
Qed.

(* Build cmInv at the join from: the frame facts, the run's footprint Wm (inside aWc), the class hint/flag readback,
   the saves and (side path) the flag word. The asan state is rebuilt by fl_fp_free / fl_tls_same / addr_munch. *)
Lemma cm_mk_inv : forall (fr sp2 jj nn : Z) (mc : word -> option byte) (Wm : list ivl),
  cmFK fr sp2 jj nn ->
  munch Wm m mc -> wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
  sub_fp Wm aWc ->
  (forall y, S - 9136 <= y < S -> app_mem y -> outside Wm (shadow_addr y)) ->
  (forall c, In c [0%nat; 1%nat; 2%nat] ->
     (exists h', bytes_at rsegs mc (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs mc (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  rw_cells rsegs mc (S - 96) cmSAVES ->
  (nn = 1 -> bytes_at rsegs mc (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) ->
  cmInv fr sp2 jj nn mc.
Proof.
  intros fr sp2 jj nn mc Wm FK MUw WMw RMw MIw SUBw SHW Hcls SAVESmc FLAGmc.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  pose proof FP0 as FPpack0.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0 & HDd0).
  pose proof HPl0 as (P1 & P2 & P3 & P4 & P5).
  split; [exact FK|].
  split; [exact (munch_weaken Wm aWc m mc SUBw MUw)|].
  split; [exact WMw|].
  split; [exact RMw|].
  split; [exact MIw|].
  split; [exact (fl_asan_cells Wm m mc AC MUw (fun x Hx => SUBw x (acl_rt_out_Wc x Hx)))|].
  split; [exact (shadow_rw_mono m mc SR WMw RMw)|].
  split.
  { apply (fl_fp_free [0%nat; 1%nat; 2%nat] m mc (bv_unsigned tp) FS (S - 9136) S aWf aDf Wm FPpack0 TLS0 MUw WMw).
    - exact SUBw.
    - intros x Hx. apply SUBw. exact (acl_hdr_out_Wc x Hx).
    - intros x Hx. right. apply RMw. exact (rd_of_stk m FS (FS + FS_SIZE) P5 x Hx).
    - exact Hcls. }
  split.
  { intros DT TS C T DB kk HTcells.
    assert (apart : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                      (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUBw. unfold aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd0 (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLS0 DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same m mc Wm (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells MUw apart)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLS0 DT TS C T DB kk HT0). }
  split.
  { assert (ADm : addressable m (sp2 - 8800) 8800).
    { apply (acl_addr_sub m (S - 9136) 9136 (sp2 - 8800) 8800 AW);
        destruct FSPc as [Esp|Esp]; try rewrite Esp; lia. }
    apply (addr_munch Wm m mc (sp2 - 8800) 8800 ADm MUw).
    intros i Hi. apply SHW.
    - destruct FSPc as [Esp|Esp]; rewrite Esp; lia.
    - right. unfold HIGHMEM_BEG, APPMEM_END. destruct FSPc as [Esp|Esp]; rewrite Esp; lia. }
  split.
  { intros x Hx _.
    pose proof AW as AWc. destruct AWc as (_ & _ & _ & AWb).
    pose proof (AWb (x - (S - 9136)) ltac:(clear -Hx; lia)) as ABx.
    replace (S - 9136 + (x - (S - 9136))) with x in ABx by (clear; lia).
    exact (cm_ab_keep Wm m mc x ABx MUw (SHW x Hx (proj1 ABx))). }
  split; [exact SAVESmc|].
  exact FLAGmc.
Qed.

(* After a class-2 frame allocation the flag byte jj reads 1 at mc and the rest of the class-2 flag array is kept by
   the run: the whole array reads back as a list of 0/1 bytes of length fs_M 2. *)
Lemma cm_flag_upd : forall (ms mc : word -> option byte) (W : list ivl) (flags : list byte) (j : Z),
  0 <= j < fs_M 2 -> Z.of_nat (length flags) = fs_M 2 ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
  bytes_at rsegs ms (fs_flag FS 2 0) flags -> munch W ms mc ->
  (forall x, fs_flag FS 2 0 <= x < fs_flag FS 2 0 + fs_M 2 -> x <> fs_flag FS 2 j -> outside W x) ->
  bytes_at rsegs mc (fs_flag FS 2 j) [Z_to_bv 8 1] ->
  exists flags', bytes_at rsegs mc (fs_flag FS 2 0) flags' /\ Z.of_nat (length flags') = fs_M 2 /\
     Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
Proof.
  intros ms mc W flags j Hj Hlen HF01 HFa MU Hout HFL.
  assert (EFj : fs_flag FS 2 j = fs_flag FS 2 0 + j) by (unfold fs_flag; lia).
  assert (Hjn : (Z.to_nat j + length [Z_to_bv 8 1] <= length flags)%nat) by (cbn [length]; lia).
  assert (Hjlen : (Z.to_nat j <= length flags)%nat) by lia.
  exists (upd_bytes flags (Z.to_nat j) [Z_to_bv 8 1]).
  split; [|split].
  - unfold upd_bytes.
    rewrite bytes_at_app. split.
    + apply (fl_bytes W ms mc (fs_flag FS 2 0) (firstn (Z.to_nat j) flags)); [| exact MU |].
      * rewrite <- (firstn_skipn (Z.to_nat j) flags) in HFa. apply bytes_at_app in HFa. exact (proj1 HFa).
      * intros x Hx. rewrite firstn_length in Hx.
        apply Hout; [unfold fs_flag in *; lia | unfold fs_flag in *; lia].
    + rewrite firstn_length. replace (Z.of_nat (Nat.min (Z.to_nat j) (length flags))) with j by lia.
      rewrite bytes_at_app. split.
      * rewrite <- EFj. exact HFL.
      * cbn [length].
        apply (fl_bytes W ms mc (fs_flag FS 2 0 + j + 1) (skipn (Z.to_nat j + 1) flags)); [| exact MU |].
        -- rewrite <- (firstn_skipn (Z.to_nat j + 1) flags) in HFa. apply bytes_at_app in HFa.
           rewrite firstn_length in HFa.
           replace (Z.of_nat (Nat.min (Z.to_nat j + 1) (length flags))) with (j + 1) in HFa by lia.
           replace (fs_flag FS 2 0 + j + 1) with (fs_flag FS 2 0 + (j + 1)) by lia. exact (proj2 HFa).
        -- intros x Hx. rewrite skipn_length in Hx.
           apply Hout; [unfold fs_flag in *; lia | unfold fs_flag in *; lia].
  - rewrite upd_bytes_length by exact Hjn. exact Hlen.
  - unfold upd_bytes. apply Forall_app; split; [apply cm_forall_firstn; exact HF01|].
    apply Forall_app; split; [repeat constructor; right; reflexivity | apply cm_forall_skipn; exact HF01].
Qed.


(* A side-stack header byte (a hint or flag of class 0/1/2) is apart from the side-arm footprint: the data ranges by
   lia (with FShi, Hfrlo, the jj bound), the frame's shadow range by acl_sh_out (app vs shadow). *)
Ltac cm_hdr_out HFSapp HHm8 :=
  cbn [outside]; unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in *
               | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in *
               | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in *
               | change (2 ^ (15 - 2)) with 8192 in * ];
  repeat split; try exact I;
  first
    [ lia
    | match goal with
      | |- ~ (shadow_addr ?frr <= ?xx < _) =>
          let A := fresh "A" in let B := fresh "B" in intros [A B];
          pose proof (acl_sh_out xx frr (frr + 8 * 32) ltac:(apply HFSapp; unfold FS_SIZE; lia)
                        ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso;
          rewrite (cm_sh_add8 frr 32 HHm8) in Hso; apply Hso; split; [exact A | exact B]
      end ].

Lemma cm_entry : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cmKB Q ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K.
  unfold REAC_BOX_CATALOGUE_MATCH.
  assert (STbox : stk rsegs m (S - 9136) S /\ True) by (split; [exact ST | exact I]).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  pose proof AC as (CK & GCK & _ & _ & _ & UA & GUA & _).
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
  apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
  unfold REAL_BCMP, REAL_MEMCMP, GOT_CF, CF in HBCMP, HMEMCMP, HGOT, HCF254, HCF255.
  assert (MU : munch [(S - 9136, S)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  assert (RM : rd_mono m m) by apply rd_mono_refl.
  pose proof ST as ST0.
  carve_frame 96%nat ST0.
  step.
  assert (HSz : store_ok rsegs m (wa (S - 128)) 8 = true)
    by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m (S - 9136) (S - 96)); [exact ST0 | lia] |
        apply wmono_refl | lia | lia]).
  step. store_done.
  do 12 step.
  step. step.
  assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = CA).
  { rewrite unsigned_lit by lia. rewrite land_align32 by lia. unfold CA.
    replace (S + -128) with (S - 128) by lia. reflexivity. }
  rewrite EA.
  do 8 step.
  step. step.
  replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
  step. step.
  (* transport fp to the pre-malloc memory m0 *)
  pose proof (fl_fp [0%nat;1%nat;2%nat] m m0 (bv_unsigned tp) FS (S - 9136) S [] aDf
                [(S - 9136, S)] FP0 MU WM ltac:(intros x Hx; exact Hx)) as FP1.
  destruct FP1 as (DT & TS & C & T & DB & kk & HT1 & HTP1 & HPl1 & H881 & H961 & HCL1 & HFS1 & HAPP1 & HWd1 & HDd1).
  pose proof HCL1 as HCL1'. do 2 apply Forall_cons_iff in HCL1' as [_ HCL1']. apply Forall_cons_iff in HCL1' as [HC2 _].
  destruct HC2 as (_ & h & flags & HH2 & HF2 & HFl2 & HFb2).
  pose proof HWd1 as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  (* asan state at m0 *)
  assert (AC0 : asan_cells m0).
  { apply (fl_asan_cells [(S - 9136, S)] m m0 AC MU). intros x Hx. unfold RT_LO, RT_HI in Hx.
    cbn [outside]. split; [clear -Hx HHM'; lia | exact I]. }
  pose proof (shadow_rw_mono m m0 SR WM RM) as SR0.
  pose proof (stk_split rsegs m0 (S - 9136) CA (S - 96) ST0 ltac:(lia)) as [STA _].
  pose proof HSM as HM. unfold asan_stack_malloc_2_contract, asan_stack_malloc_contract in HM. cbv zeta in HM.
  eapply evt_cut.
  { eapply HM with (lo := S - 9136) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
      (DB := DB) (k := kk) (flags := flags).
    all: rewrite ?(unsigned_lit CA), ?(unsigned_lit 192) by lia.
    - unfold fs_B; cbn; lia.
    - reflexivity.
    - exact AC0.
    - exact SR0.
    - exact MI.
    - exact HT1.
    - intros Hc; lia.
    - exact HTP1.
    - exact HPl1.
    - exact H881.
    - exact H961.
    - exact HH2.
    - exact HF2.
    - exact HFl2.
    - exact HFb2.
    - exact STA.
    - unfold ASAN_STACK_MALLOC_K; lia.
    - unfold ASAN_STACK_MALLOC_K; clear -HFS1 CAlo2 CAhi2; lia.
    - intros a Ha; apply HAPP1; unfold ASAN_STACK_MALLOC_K in Ha; clear -Ha CAlo2 CAhi2; lia.
    - cbn [disjoint_from]; unfold ASAN_STACK_MALLOC_K; repeat split; try exact I;
        match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
          match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end. }
  intros ms' PO.
  destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E &
                  WM2 & MI2 & ST2 & FSP2 & (h2 & HH2') & ALT).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 541960)) with (Z_to_bv 64 541960)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step. step. step.
  pose proof acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  rewrite (unsigned_lit CA) in ST2 by lia.
  pose proof FP0 as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & _ & _ & _ & HCLx & _).
  pose proof HCLx as HCLy.
  apply Forall_cons_iff in HCLy as [(_ & h0 & flags0 & HH0 & HF0 & HFl0 & HFb0) HCLy1].
  apply Forall_cons_iff in HCLy1 as [(_ & h1 & flags1 & HH1 & HF1 & HFl1 & HFb1) HCLy2].
  apply Forall_cons_iff in HCLy2 as [(_ & h2m & flags2m & HH2m & HF2m & HFl2m & HFb2m) _].
  destruct ALT as [(Hall & Ex0 & MUf) | (ii & Hii0 & Hiipre & Hiinth & FRM)].
  - (* ================= real-stack arm (fr = CA - 192) ================= *)
    subst x0.
    replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
    rewrite (unsigned_lit CA) in MUf by lia. unfold ASAN_STACK_MALLOC_K in MUf.
    assert (RM2r : rd_mono m0 m2).
    { apply (rd_mono_list _ _ _ MUf). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_bytes _ _ _ HH2'). rewrite length_le8. cbn [Z.of_nat]. unfold fs_hint in *. lia.
      - apply (rd_of_stk _ _ _ ST2). lia. }
    assert (RMr : rd_mono m m2) by (apply (rd_mono_trans _ _ _ RM RM2r)).
    assert (WMr : wmono rsegs m m2) by (apply (wmono_trans _ _ _ _ WM WM2)).
    assert (FR2 : rw_cells rsegs m2 (S - 96) cmSAVES).
    { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MUf WM2).
      cbn [disjoint_from cells_size csize Nat.add cmSAVES]. unfold fs_hint. repeat split; lia. }
    assert (MUr : munch [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8)] m m2).
    { apply (munch_trans _ m m0 m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *.
        destruct Hx as (Hw & _). split; [exact Hw | exact I].
      - eapply munch_weaken; [|exact MUf]. intros x Hx. cbn [outside] in *.
        destruct Hx as (Hw & Hh & _). split; [exact Hh | split; [clear -Hw CAlo2 CAhi2; lia | exact I]]. }
    clear MUf.
    step. step.
    match goal with |- context [Z.land ?x 18446744073709551584] =>
      replace (Z.land x 18446744073709551584) with (CA - 192)
        by (rewrite ?(unsigned_lit CA), ?unsigned_lit by lia; rewrite land_align32 by lia;
            Z.div_mod_to_equations; lia) end.
    step. step.
    rewrite (unsigned_lit CA) by lia.
    assert (HSz2 : store_ok rsegs m2 (wa (CA - 4096)) 8 = true)
      by (eapply wv_store_ok;
          [intros i Hi; apply (stk_wv m2 (S - 9136) CA); [exact ST2 | lia] | apply wmono_refl | lia | lia]).
    step. store_done.
    step.
    rewrite (rc_lts_signed (CA - 192) (CA - 4096)) by lia.
    replace (CA - 192 <? CA - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step.
    clear ST; destruct STbox as [ST _].
    eapply (cm_header Q (CA - 192) (CA - 192) 0 0 _); [exact K|].
    apply (cm_mk_inv (CA - 192) (CA - 192) 0 0 _ [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8)]).
    + left. split; [reflexivity | split; [reflexivity | split; reflexivity]].
    + exact MUr.
    + exact WMr.
    + exact RMr.
    + exact MI2.
    + intros x Hx. unfold aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hw & Hxs).
      unfold aXs in Hxs. apply cm_out_app in Hxs. destruct Hxs as (Hfpw & _).
      cbn [outside]. split; [exact Hw | split; [|exact I]].
      exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))).
    + intros y Hy Hap. pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [outside]. split; [|split; [|exact I]].
      * unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        clear -Hsh Hy HHM'. lia.
      * apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
        intros z Hz. apply FSapp. unfold fs_hint in *. unfold FS_SIZE. lia.
    + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
      * split.
        -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (le8 h0) HH0 MUr).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cbn [outside]. unfold fs_hint in *. split; [lia | split; [lia | exact I]].
        -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
           apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUr).
           intros x Hx. rewrite HFl0 in Hx. cbn [outside].
           unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 0)) with 32768 in *;
             change (2 ^ (14 - 0)) with 16384 in *; unfold fs_hint in *.
           split; [lia | split; [lia | exact I]].
      * split.
        -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (le8 h1) HH1 MUr).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cbn [outside]. unfold fs_hint in *. split; [lia | split; [lia | exact I]].
        -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
           apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUr).
           intros x Hx. rewrite HFl1 in Hx. cbn [outside].
           unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 1)) with 16384 in *;
             change (2 ^ (14 - 1)) with 8192 in *; unfold fs_hint in *.
           split; [lia | split; [lia | exact I]].
      * split.
        -- destruct (rd8_le8 _ (fs_hint FS 2)
             ltac:(unfold fs_hint; lia) ltac:(unfold fs_hint; lia)
             ltac:(intros i Hi; apply RMr; apply (rd_of_bytes _ _ _ HH2m);
                   rewrite length_le8; cbn [Z.of_nat]; unfold fs_hint; lia)) as (hw & Hhw).
           exists hw. exact Hhw.
        -- exists flags2m. split; [|split; [exact HFl2m | exact HFb2m]].
           apply (fl_bytes _ m _ (fs_flag FS 2 0) flags2m HF2m MUr).
           intros x Hx. rewrite HFl2m in Hx. cbn [outside].
           unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *;
             change (2 ^ (14 - 2)) with 4096 in *; unfold fs_hint in *.
           split; [lia | split; [lia | exact I]].
    + exact FR2.
    + intros Hcontra; discriminate Hcontra.
  - (* ================= side-stack arm (fr = fs_frame FS 2 jj) ================= *)
    unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
    rewrite (unsigned_lit CA) in FRM by lia.
    rewrite (unsigned_lit 192) in FRM by lia.
    replace (fs_B 2) with 256 in FRM by reflexivity.
    replace (fs_shadow_n 2 192) with 32 in FRM by reflexivity.
    destruct FRM as (Ex0 & Hm64 & _ & HFL & H24 & Hflagword & HSH & HADD & STF & APF & FSlo & FShi' & GT & FRA' & DIS & MU2).
    remember ((bv_unsigned h + ii) mod fs_M 2) as jj eqn:Ejj.
    assert (Hjj : 0 <= jj < fs_M 2) by (subst jj; apply Z.mod_pos_bound; reflexivity).
    remember (fs_frame FS 2 jj) as fr eqn:Efr.
    subst x0.
    unfold FS_SIZE in FShi'. change (fs_M 2) with 4096 in Hjj.
    unfold ASAN_STACK_MALLOC_K in MU2.
    replace (fr + 256 - 8) with (fr + 248) in * by lia.
    assert (Hm8 : fr mod 8 = 0) by (clear -Hm64; Z.div_mod_to_equations; lia).
    unfold ASAN_GT in GT.
    assert (Hfrlo : FS + 36864 <= fr) by
      (rewrite Efr; unfold fs_frame, fs_B; cbn [Z.of_nat]; change (2 ^ 20) with 1048576; change (2 ^ 2) with 4; lia).
    rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
    assert (RM2r : rd_mono m0 m2).
    { apply (rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_bytes _ _ _ HH2'). rewrite length_le8. cbn [Z.of_nat]. unfold fs_hint in *. lia.
      - apply (rd_of_bytes _ _ _ HFL). cbn [length]. lia.
      - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn [Z.of_nat]. lia.
      - apply (rd_of_bytes _ _ _ Hflagword). rewrite length_le8. cbn [Z.of_nat]. lia.
      - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
      - apply (rd_of_stk _ _ _ ST2). lia. }
    assert (RMw : rd_mono m m2) by (apply (rd_mono_trans _ _ _ RM RM2r)).
    assert (WMw : wmono rsegs m m2) by (apply (wmono_trans _ _ _ _ WM WM2)).
    assert (FR2 : rw_cells rsegs m2 (S - 96) cmSAVES).
    { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add cmSAVES].
      unfold fs_hint, fs_flag, fs_M. cbn [Z.of_nat]. change (2 ^ 15) with 32768. change (2 ^ (15 - 2)) with 8192.
      repeat split; right; first [ lia | (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia) ]. }
    assert (MUw : munch [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                         (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)] m m2).
    { apply (munch_trans _ m m0 m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *.
        split; [exact (proj1 Hx) | exact I].
      - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx. exact (proj2 Hx). }
    clear ST; destruct STbox as [ST _].
    eapply (cm_header Q fr CA jj 1 m2); [exact K|].
    apply (cm_mk_inv fr CA jj 1 m2 [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                     (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]).
    + right. split; [exact Hjj | split; [exact Efr | split; reflexivity]].
    + exact MUw.
    + exact WMw.
    + exact RMw.
    + exact MI2.
    + intros x Hx. unfold aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hwn & Hxs).
      unfold aXs in Hxs. apply cm_out_app in Hxs. destruct Hxs as (Hfpw & Hws).
      cbn [outside] in Hws. destruct Hws as (Hws & _).
      cbn [outside]. split; [exact Hwn|]. split.
      { exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))). }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_flag FS 2 ltac:(cbn; tauto))).
        unfold fs_flag, fs_M in *. destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
        destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
        destruct Hc. split; lia. }
      split.
      { pose proof (out_in _ _ _ _ Hfpw (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as HFin.
        assert (GE : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr).
        { apply acl_sh_ge. rewrite Efr. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. lia. }
        assert (LE : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
        { rewrite Efr. unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
          change (2 ^ 20) with 1048576 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
          Z.div_mod_to_equations; lia. }
        intros [A B]. clear -HFin GE LE A B. lia. }
      split; [|exact I].
      intros Hc. apply Hwn. clear -Hc CAlo2 CAhi2. lia.
    + intros y Hy Hap. pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [outside]. split.
      { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        clear -Hsh Hy HHM'. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
        intros z Hz. apply FSapp. unfold fs_hint in *. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
        intros z Hz. apply FSapp. unfold fs_flag, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 15) with 32768 in *. change (2 ^ (15 - 2)) with 8192 in *. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 24) (fr + 32) Hsh).
        intros z Hz. apply APF. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 248) (fr + 256) Hsh).
        intros z Hz. apply APF. lia. }
      split; [|split; [|exact I]].
      { intros [A B]. pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
        rewrite (cm_sh_add8 fr 32 Hm8) in G. lia. }
      { apply (sh_out_app (shadow_addr y) (CA - 208) CA Hsh).
        intros z Hz. right. unfold HIGHMEM_BEG, APPMEM_END. clear -Hz Hy HHM' HAE' CAlo2 CAhi2. lia. }
    + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
      * split.
        -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (le8 h0) HH0 MUw).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8.
        -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
           apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUw).
           intros x Hx. rewrite HFl0 in Hx.
           cm_hdr_out FSapp Hm8.
      * split.
        -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (le8 h1) HH1 MUw).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8.
        -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
           apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUw).
           intros x Hx. rewrite HFl1 in Hx.
           cm_hdr_out FSapp Hm8.
      * split.
        -- exists h2. exact HH2'.
        -- apply (cm_flag_upd m0 m2
             [(fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
              (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]
             flags jj Hjj HFl2 HFb2 HF2 MU2); [| exact HFL].
           intros x Hx Hxne.
           assert (Hxap : app_mem x) by (apply FSapp; unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; unfold FS_SIZE; lia).
           cbn [outside]. split.
           { unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
           split.
           { intros [A B]. apply Hxne. unfold fs_flag in *. lia. }
           split.
           { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
           split.
           { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
           split; [|split; [|exact I]].
           { intros [A B]. pose proof (acl_sh_out x fr (fr + 8 * 32) Hxap ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso.
             rewrite (cm_sh_add8 fr 32 Hm8) in Hso. apply Hso. split; [exact A | exact B]. }
           { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
    + exact FR2.
    + intros _. exact Hflagword.
Qed.

(* ============================ (b) gate ============================ *)

(* The input buffer at f is apart from the caller footprint aWc (window, side stack, window shadow): it is a data
   range (aDf) apart from fp_w, below or above the window, and application memory apart from the window shadow. *)
Lemma cm_f_out : 50 <= len -> forall x, f <= x < f + 50 -> outside aWc x.
Proof.
  intros HL x Hx. destruct (HF HL) as (Hf0 & Hf50 & _ & Hdj). destruct (AFU HL) as (AFm & _).
  assert (Hap : app_mem x).
  { pose proof (acl_app_in m f 50 (x - f) AFm ltac:(lia)) as H.
    replace (f + (x - f)) with x in H by lia. exact H. }
  apply acl_out_Wc; [exact Hap | lia | ].
  apply (acl_out_fpw_d f (f + 50) x);
    [ unfold aDf; replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; lia); left; reflexivity | lia ].
Qed.

Lemma cm_f_sh_out : 50 <= len -> forall i, 0 <= i < 50 -> outside aWc (shadow_addr (f + i)).
Proof.
  intros HL i Hi. destruct (HF HL) as (_ & _ & _ & Hdj). destruct (AFU HL) as (AFm & _).
  apply acl_out_Wc_sh.
  - exact (acl_app_in m f 50 i AFm Hi).
  - apply (acl_out_fpw_d f (f + 50) (f + i));
      [ unfold aDf; replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; lia); left; reflexivity | lia ].
  - lia.
Qed.

(* The 50 bytes at f stay addressable in any memory the run reached writing only aWc. *)
Lemma cm_AF : forall mc', 50 <= len -> munch aWc m mc' -> addressable mc' f 50.
Proof.
  intros mc' HL MU. destruct (AFU HL) as (AFm & _).
  apply (acl_addr_munch aWc m mc' f 50 AFm MU). intros i Hi. exact (cm_f_sh_out HL i Hi).
Qed.

(* The 50 input bytes read back as fb in such a memory. *)
Lemma cm_FB : forall mc', 50 <= len -> munch aWc m mc' -> bytes_at rsegs mc' f fb.
Proof.
  intros mc' HL MU. destruct (HF HL) as (_ & _ & HFb & _).
  apply (fl_bytes aWc m mc' f fb HFb MU).
  intros x Hx. apply (cm_f_out HL x).
  rewrite Hfb in Hx. change (Z.of_nat 50) with 50 in Hx. exact Hx.
Qed.

(* After the un-poisoning stores (shadow bytes 4..8 -> 0,0,0,0,4), the parse buffer [fr + 32, fr + 68) is
   addressable: the four 0 bytes make 32 granules usable, the 0x04 byte the first 4 of the next granule. *)
Lemma cm_parse_addr : forall (mc0 : word -> option byte) (fr0 : Z),
  fr0 mod 8 = 0 -> 0 <= fr0 -> fr0 + 68 <= APPMEM_END ->
  (forall i, 0 <= i < 36 -> app_mem (fr0 + 32 + i)) ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 4) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 5) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 6) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 7) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 8) [Z_to_bv 8 4] ->
  addressable mc0 (fr0 + 32) 36.
Proof.
  intros mc0 fr0 Hm Hfr Hhi Hap B4 B5 B6 B7 B8.
  assert (D : forall A v, bytes_at rsegs mc0 A [v] -> mrd rsegs mc0 (wa A) = Some v).
  { intros A v (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as HH. cbn in HH.
    rewrite Z.add_0_r in HH. exact HH. }
  pose proof (D _ _ B4) as R4. pose proof (D _ _ B5) as R5. pose proof (D _ _ B6) as R6.
  pose proof (D _ _ B7) as R7. pose proof (D _ _ B8) as R8.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
  intros i Hi. split; [apply Hap; exact Hi|].
  destruct (Z_lt_le_dec i 8) as [c0|c0];
    [| destruct (Z_lt_le_dec i 16) as [c1|c1];
       [| destruct (Z_lt_le_dec i 24) as [c2|c2];
          [| destruct (Z_lt_le_dec i 32) as [c3|c3]]]].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 4)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R4
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 5)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R5
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 6)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R6
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 7)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R7
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 4). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 8)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R8
      | unfold shadow_ok; right; change (bv_signed (Z_to_bv 8 4)) with 4;
        split; [ Z.div_mod_to_equations; lia | lia ] ].
Qed.

(* The register state at the reac_ctrl_parse call (pc 0x84684): a0 = f, a1 = len, a2 = fr + 32 (the parse buffer),
   s0 = S, s1 = CA, s2 = frame, s3 = f, s4 = len, s5 = ASAN_K, s6 = shadow_addr fr, s7 = fr; the input is at least
   50 bytes and its four header bytes 12, 13, 16, 17 are 0x88 0x19 0xcd 0xea (the first five tests of RcMatch's
   cm_gate passed), the invariant holds at mc and the parse buffer is addressable. *)
Definition cmPB (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
    cmInv fr sp2 jj nn mc -> addressable mc (fr + 32) 36 ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84684) fc None mc (seg_rom rsegs)).

(* The register state at the catalogue-miss tail (pc 0x84720): the short-input branch of `bltu len,50` and the four
   header-byte mismatch branches all reach it with the invariant unchanged at mc, and there the result the contract
   names is 0 (want CM_T len fb = 0). *)
Definition cmMiss (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = 0 -> cmInv fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84720) fc None mc (seg_rom rsegs)).

(* A short input or a header byte other than 0x88 / 0x19 / 0xcd / 0xea at 12 / 13 / 16 / 17 makes RcMatch's
   cm_gate false, so the result is 0. *)
Lemma cm_miss_short : len < 50 -> want CM_T len fb = 0.
Proof.
  intros L. apply cm_gate_false. unfold RcMatch.cm_gate. rewrite (proj2 (Z.leb_gt 50 len) L). reflexivity.
Qed.

Lemma cm_miss_hdr : forall k c, 50 <= len ->
  (k = 12%nat /\ c = 136 \/ k = 13%nat /\ c = 25 \/ k = 16%nat /\ c = 205 \/ k = 17%nat /\ c = 234) ->
  bv_unsigned (nth k fb (Z_to_bv 8 0)) <> c -> want CM_T len fb = 0.
Proof.
  intros k c L Hk Hne. apply cm_gate_false. unfold RcMatch.cm_gate, cp_v, cp_b, cp_z.
  rewrite (proj2 (Z.leb_le 50 len) L).
  destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; rewrite (proj2 (Z.eqb_neq _ _) Hne);
    rewrite ?andb_false_r; reflexivity.
Qed.

(* After a 1-byte store at E (pc already past it): keep the stored bytes as a bytes_at fact HB on the written memory
   (store_done's remember renames that memory in HB too), then store_done. *)
Ltac cm_keep HB :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (HB : bytes_at segs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; simpl_sizes; lia);
      store_done
  end.

(* The run from the gate at 0x845dc to the reac_ctrl_parse call: `bltu len,50` (short input -> the miss tail), then
   the four shadow-checked loads of f+12, f+13, f+16, f+17 (each instrumented check passes from `addressable mc f 50`,
   so the call of __asan_report_* is not reached; each header byte is compared: a mismatch -> the miss tail), then
   the un-poisoning of the parse buffer's shadow (bytes 4..8 -> 0,0,0,0,4), ending at the call entry with
   `addressable (fr + 32) 36` (cmPB). *)
Lemma cm_gate : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  cmPB Q -> cmMiss Q -> cmInv fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 KP KM INV.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & _).
  step.
  rewrite cm_ltu_lit by (clear -Rlen; lia).
  destruct (Z.ltb_spec len 50) as [L|L]; cbv iota.
  { eapply KM; [exact (cm_miss_short L) | exact INVk]. }
  destruct (HF L) as (Hf0 & Hf50 & _ & _).
  pose proof (cm_FB mc L MUg) as BF.
  pose proof (cm_AF mc L MUg) as AF.
  clear MUg.
  pose proof (rd_byte rsegs mc f fb 12 BF ltac:(rewrite Hfb; clear; lia)) as R12.
  pose proof (rd_byte rsegs mc f fb 13 BF ltac:(rewrite Hfb; clear; lia)) as R13.
  pose proof (rd_byte rsegs mc f fb 16 BF ltac:(rewrite Hfb; clear; lia)) as R16.
  pose proof (rd_byte rsegs mc f fb 17 BF ltac:(rewrite Hfb; clear; lia)) as R17.
  change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
  change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
  clear BF.
  pose proof (byte_range (nth 12 fb (Z_to_bv 8 0))) as BR12. pose proof (byte_range (nth 13 fb (Z_to_bv 8 0))) as BR13.
  pose proof (byte_range (nth 16 fb (Z_to_bv 8 0))) as BR16. pose proof (byte_range (nth 17 fb (Z_to_bv 8 0))) as BR17.
  assert (RX12 : 0 <= f + 12 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX13 : 0 <= f + 13 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX16 : 0 <= f + 16 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX17 : 0 <= f + 17 < 2^64) by (clear -Hf0 Hf50; lia).
  pose proof (acl_shadow mc f 50 12 1 (f + 12) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 eq_refl); clear -H; lia) eq_refl) as SH12.
  pose proof (acl_shadow mc f 50 13 1 (f + 13) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 eq_refl); clear -H; lia) eq_refl) as SH13.
  pose proof (acl_shadow mc f 50 16 1 (f + 16) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 16) 8 eq_refl); clear -H; lia) eq_refl) as SH16.
  pose proof (acl_shadow mc f 50 17 1 (f + 17) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 17) 8 eq_refl); clear -H; lia) eq_refl) as SH17.
  clear AF.
  (* byte 12: 0x88 *)
  step.
  chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 12 fb (Z_to_bv 8 0))) 136) as [E12|E12]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 12%nat 136 L ltac:(clear; lia) E12) | exact INVk]. }
  (* byte 13: 0x19 *)
  step.
  chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 13 fb (Z_to_bv 8 0))) 25) as [E13|E13]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 13%nat 25 L ltac:(clear; lia) E13) | exact INVk]. }
  (* byte 16: 0xcd *)
  step.
  chk_core (f + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 16 fb (Z_to_bv 8 0))) 205) as [E16|E16]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 16%nat 205 L ltac:(clear; lia) E16) | exact INVk]. }
  (* byte 17: 0xea *)
  step.
  chk_core (f + 17) RX17 (Z_to_bv 5 12) SH17 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 17 fb (Z_to_bv 8 0))) 234) as [E17|E17]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 17%nat 234 L ltac:(clear; lia) E17) | exact INVk]. }
  clear R12 R13 R16 R17 BR12 BR13 BR16 BR17 RX12 RX13 RX16 RX17.
  (* the un-poisoning of the parse buffer's shadow bytes 4..8 (all inside cmHF fr) *)
  step.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & _ & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia). unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall i, 0 <= i < 24 -> wview rsegs m (wa (shadow_addr fr + i)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold cmHF in MUh.
  cm_wst (shadow_addr fr + 4) 1%nat. step. cm_keep B4.
  cm_wst (shadow_addr fr + 5) 1%nat. step. cm_keep B5.
  cm_wst (shadow_addr fr + 6) 1%nat. step. cm_keep B6.
  cm_wst (shadow_addr fr + 7) 1%nat. step. cm_keep B7.
  step.
  cm_wst (shadow_addr fr + 8) 1%nat. step. cm_keep B8.
  step. step.
  eapply KP; [exact L | exact E12 | exact E13 | exact E16 | exact E17 | |].
  - eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
  - eapply cm_parse_addr; [exact FR8 | clear -FRpos; lia | clear -FRhi HAE; lia | | exact B4 | exact B5 | exact B6
                          | exact B7 | exact B8].
    intros i Hi. replace (fr + 32 + i) with (fr + (32 + i)) by (clear; lia). apply FAP. clear -Hi; lia.
Qed.

(* ============================ (c) the calls ============================ *)

(* The window and the frame read back in any memory the run reached (wmono, rd_mono from m; the side stack's stk). *)
Lemma cm_stk_win : forall fr sp2 jj nn mc, cmInv fr sp2 jj nn mc -> stk rsegs mc (S - 9136) S.
Proof.
  intros fr sp2 jj nn mc (_ & _ & WM & RM & _).
  destruct ST as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hv & Hb). split; [apply WM, Hv | apply RM, Hb].
Qed.

Lemma cm_stk_fr : forall fr sp2 jj nn mc, cmInv fr sp2 jj nn mc -> stk rsegs mc fr (fr + 192).
Proof.
  intros fr sp2 jj nn mc INV. pose proof (cm_stk_win fr sp2 jj nn mc INV) as SW.
  destruct INV as (FK & _ & _ & _ & _ & _ & _ & FP & _).
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst fr. destruct (stk_split rsegs mc (S - 9136) (CA - 192) S SW ltac:(lia)) as (_ & SW2).
    destruct (stk_split rsegs mc (CA - 192) (CA - 192 + 192) S SW2 ltac:(lia)) as (SW3 & _). exact SW3.
  - destruct FP as (DT & TS & C & T & DB & k & _ & _ & (_ & _ & _ & _ & P5) & _).
    assert (LO : FS <= fr) by (rewrite Ef; unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (HI : fr + 192 <= FS + FS_SIZE).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M, FS_SIZE in *. cbn [Z.of_nat] in *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
    destruct (stk_split rsegs mc FS fr (FS + FS_SIZE) P5 ltac:(lia)) as (_ & P6).
    destruct (stk_split rsegs mc fr (fr + 192) (FS + FS_SIZE) P6 ltac:(lia)) as (P7 & _). exact P7.
Qed.

(* A point outside a footprint is outside any footprint whose ranges are among its ranges. *)
Lemma out_incl : forall W W' x, incl W' W -> outside W x -> outside W' x.
Proof.
  intros W W' x. induction W' as [|[a b] W' IH]; intros Hi Ho; cbn [outside]; [exact I|]. split.
  - exact (out_in W a b x Ho (Hi _ (or_introl eq_refl))).
  - apply IH; [intros r Hr; apply Hi; right; exact Hr | exact Ho].
Qed.

Lemma cm_out_fpw_c : forall c x, In c [0%nat; 1%nat; 2%nat] -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  outside (fp_w [c] FS) x.
Proof. intros c x Hc Ho. exact (out_incl _ _ x (fp_w_incl c _ FS Hc) Ho). Qed.

(* An application byte apart from the hint word, the flag bytes and the frames of class c (c <= 2) is apart from
   fp_w [c] FS (the frames' shadow bytes are shadow memory). *)
Lemma cm_fpw1_out : forall c x, (c <= 2)%nat -> app_mem x ->
  (x < fs_hint FS c \/ fs_hint FS c + 8 <= x) -> (x < fs_flag FS c 0 \/ fs_flag FS c 0 + fs_M c <= x) ->
  (x < fs_frame FS c 0 \/ fs_frame FS c (fs_M c) <= x) -> outside (fp_w [c] FS) x.
Proof.
  intros c x Hc Hap H1 H2 H3. destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. unfold FS_SIZE, APPMEM_END in *.
  cbn [fp_w flat_map fp_w1 app outside]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
  apply acl_sh_out; [exact Hap | |]; unfold fs_frame, fs_M, fs_B;
    destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat]; try lia;
    unfold APPMEM_END; lia.
Qed.

Lemma cm_fpw3_out : forall x, outside (fp_w [0%nat] FS) x -> outside (fp_w [1%nat] FS) x ->
  outside (fp_w [2%nat] FS) x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros x H0 H1 H2. cbn [fp_w flat_map] in *. rewrite app_nil_r in H0, H1, H2.
  apply fl_out_app; [exact H0|]. apply fl_out_app; [exact H1|]. rewrite app_nil_r. exact H2.
Qed.

(* A byte below ASAN_GT (the image: the table, the runtime's cells, the bcmp wrapper's cells) is apart from the
   side-stack bytes, from the caller footprint aWc, and so is its shadow byte. *)
Lemma acl_out_fpw_lo : forall x, 0 <= x < ASAN_GT -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros x Hx. destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, ASAN_GT in *; lia).
  apply cm_fpw3_out; apply cm_fpw1_out; try lia; try exact Hap;
    left; unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

Lemma cm_lo_out : forall x, 0 <= x < ASAN_GT -> outside aWc x.
Proof.
  intros x Hx. pose proof HHM as HHM'. unfold HIGHMEM_BEG, ASAN_GT in *.
  apply acl_out_Wc; [unfold app_mem, LOWMEM_END; lia | lia | apply acl_out_fpw_lo; unfold ASAN_GT; lia].
Qed.

Lemma cm_lo_sh_out : forall x, 0 <= x < ASAN_GT -> outside aWc (shadow_addr x).
Proof.
  intros x Hx. pose proof HHM as HHM'. unfold HIGHMEM_BEG, ASAN_GT in *.
  apply acl_out_Wc_sh; [unfold app_mem, LOWMEM_END; lia | apply acl_out_fpw_lo; unfold ASAN_GT; lia | lia].
Qed.

Lemma cm_lo_bytes : forall mc A bs, munch aWc m mc -> bytes_at rsegs m A bs -> 0 <= A ->
  A + Z.of_nat (length bs) <= ASAN_GT -> bytes_at rsegs mc A bs.
Proof. intros mc A bs MU HB H0 H1. apply (fl_bytes aWc m mc A bs HB MU). intros x Hx. apply cm_lo_out. lia. Qed.

Lemma cm_lo_addr : forall mc A n, munch aWc m mc -> addressable m A n -> A + n <= ASAN_GT -> addressable mc A n.
Proof.
  intros mc A n MU HA H1. pose proof HA as (H0 & Hn & _).
  apply (acl_addr_munch aWc m mc A n HA MU). intros i Hi. apply cm_lo_sh_out. lia.
Qed.

(* The 3256 table bytes at CM_T read back as CM_TBL in any memory the run reached writing only aWc. *)
Lemma cm_tbl : forall mc, munch aWc m mc -> bytes_at rsegs mc CM_T CM_TBL.
Proof.
  intros mc MU. apply cm_lo_bytes; [exact MU | | unfold CM_T; lia | rewrite CM_TBL_len; unfold CM_T, ASAN_GT; lia].
  apply (cm_bytes_img rsegs m CM_T 3256 CM_TBL CM_TBL_eq); [unfold CM_T; lia | unfold CM_T; lia |].
  intros a Ha. apply HT. change (Z.of_nat 3256) with 3256 in Ha. exact Ha.
Qed.

(* The frame geometry: the real-stack frame is the body's sp (fr = sp2 = CA - 192), a side-stack frame is the class-2
   frame jj (FS + 2134016 + 256 jj) with sp2 = CA. *)
Lemma cm_geo : forall fr sp2 jj nn, cmFK fr sp2 jj nn ->
  fr mod 8 = 0 /\ FS + 36864 <= fr /\ sp2 mod 16 = 0 /\ S - 336 <= sp2 <= S - 128 /\
  ((nn = 0 /\ fr = sp2 /\ fr + 192 <= S - 128) \/
   (nn = 1 /\ FS + 2134016 + 256 * jj = fr /\ 0 <= jj < 4096 /\ fr + 256 <= FS + 3182592 /\ fr + 256 <= S - 9136)).
Proof.
  intros fr sp2 jj nn FK.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr sp2 nn.
  - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. left. lia.
  - unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
    change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
    split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. right. lia.
Qed.

Lemma cm_fr2 : fs_frame FS 2 0 = FS + 2134016 /\ fs_frame FS 2 (fs_M 2) = FS + 3182592.
Proof.
  unfold fs_frame, fs_B, fs_M. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. change (2 ^ 2) with 4.
  change (2 ^ (14 - 2)) with 4096. lia.
Qed.

(* A callee of class c whose window [sp2' - K, sp2') is inside the caller's: its tls premise from aTL. *)
Lemma cm_tls_call : forall mc c K sp2', aTL mc -> In c [0%nat; 1%nat; 2%nat] -> S - 9136 <= sp2' - K -> sp2' <= S ->
  forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
    fp_dj (fp_tls (bv_unsigned tp) DT TS C T DB kk) (fp_w [c] FS ++ [(shadow_addr (sp2' - K), shadow_addr sp2')]).
Proof.
  intros mc c K sp2' TL Hc H1 H2 DT TS C T DB kk HTc.
  pose proof (TL DT TS C T DB kk HTc) as H. unfold aXs in H.
  pose proof (fl_dj_last _ (fp_w [0%nat; 1%nat; 2%nat] FS) (shadow_addr (S - 9136)) (shadow_addr S)
                (shadow_addr (sp2' - K)) (shadow_addr sp2') H (acl_sh_ge _ _ H1) (acl_sh_ge _ _ H2)) as H'.
  exact (fp_dj_incl _ _ _ (incl_app_app (fp_w_incl c _ FS Hc) (incl_refl _)) H').
Qed.

(* A callee of class c at sp2 with window [sp2 - K, sp2) and a buffer [fr + d, fr + d + n) of the frame: its fp from
   the invariant's fp (fp_single); the buffer of a side-stack frame is apart from the thread cells by aTL. *)
Lemma cm_fp_call : forall c fr sp2 jj nn mc K d n D',
  cmInv fr sp2 jj nn mc -> In c [0%nat; 1%nat; 2%nat] -> 0 <= K <= 8800 -> 0 <= d -> 0 <= n -> d + n <= 192 ->
  fp_dj D' (fp_w [c] FS) ->
  fp [c] mc (bv_unsigned tp) FS (sp2 - K) sp2 ((sp2 - K, sp2) :: [(fr + d, fr + d + n)]) D'.
Proof.
  intros c fr sp2 jj nn mc K d n D' INV Hc HKr Hd Hn Hdn HD.
  destruct INV as (FK & _ & _ & _ & _ & _ & _ & FP & TL & _).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc). pose proof cm_fr2 as (F20 & F2M).
  pose proof (fp_single c _ mc (bv_unsigned tp) FS (S - 9136) S aWf aDf Hc FP) as FPc.
  destruct FPc as (DT & TS & C & T & DB & k & HTc & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact HTc|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
  split; [exact HCL|]. split; [lia|]. split; [intros a Ha; apply HA; lia|].
  split; [|exact HD].
  unfold aWf in HWd. apply fl_dj_cons in HWd as [HW1 _].
  apply fl_dj_cons. split; [apply (fl_dj_sub _ _ _ _ _ HW1); lia|].
  apply fl_dj_cons. split; [|unfold fp_dj; constructor].
  destruct Gc as [(En & Ef & Fhi) | (En & Ef & Hj & Fhi & Fhi2)].
  - apply (fl_dj_sub _ _ _ _ _ HW1); lia.
  - pose proof (TL DT TS C T DB k HTc) as TLd. unfold aXs in TLd.
    assert (INf : In (fs_frame FS 2 0, fs_frame FS 2 (fs_M 2))
                     (fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - 9136), shadow_addr S)]))
      by (apply in_or_app; left; apply fpw3_in_frame; cbn; tauto).
    unfold fp_dj in TLd |- *. constructor; [|constructor]. apply Forall_app. split.
    + apply Forall_forall. intros [a b] Hin. cbn [fst snd].
      rewrite Forall_forall in TLd. pose proof (TLd (a, b) Hin) as Hab. rewrite Forall_forall in Hab.
      pose proof (Hab _ INf) as Hly. cbn [fst snd] in Hly. rewrite F20, F2M in Hly. unfold ly_dj in *. lia.
    + constructor; [|constructor]. cbn [fst snd]. unfold ly_dj, fs_frame. cbn [Z.of_nat]. lia.
Qed.

(* The writes of a callee of class c at sp2 with window [sp2 - K, sp2) and the frame buffer [fr + d, fr + d + n):
   the buffer, the window, the class-c side-stack bytes and the window's shadow. *)
Definition cmWc (fr sp2 K d n : Z) (c : nat) : list ivl :=
  (fr + d, fr + d + n) :: (sp2 - K, sp2) :: fp_w [c] FS ++ [(shadow_addr (sp2 - K), shadow_addr sp2)].

Lemma cm_Wc_sub : forall fr sp2 jj nn K d n c, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] -> 0 <= K <= 8800 ->
  0 <= d -> 0 <= n -> d + n <= 192 -> sub_fp (cmWc fr sp2 K d n c) aWc.
Proof.
  intros fr sp2 jj nn K d n c FK Hc HKr Hd Hn Hdn x Hout.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc). pose proof cm_fr2 as (F20 & F2M).
  unfold aWc in Hout. cbn [outside] in Hout. destruct Hout as (Hw & Hxs).
  unfold aXs in Hxs. apply cm_out_app in Hxs. destruct Hxs as (Hfpw & Hws). cbn [outside] in Hws. destruct Hws as (Hws & _).
  assert (Gs1 : shadow_addr (S - 9136) <= shadow_addr (sp2 - K)) by (apply acl_sh_ge; lia).
  assert (Gs2 : shadow_addr sp2 <= shadow_addr S) by (apply acl_sh_ge; lia).
  unfold cmWc. cbn [outside]. split; [|split; [lia|]].
  - destruct Gc as [(En & Ef & Fhi) | (En & Ef & Hj & Fhi & Fhi2)]; [lia|].
    pose proof (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as HFin. rewrite F20, F2M in HFin. lia.
  - apply fl_out_app; [exact (cm_out_fpw_c c x Hc Hfpw)|]. cbn [outside]. split; [lia | exact I].
Qed.

Lemma cm_Wc_out : forall fr sp2 K d n c x, app_mem x -> 0 <= sp2 - K -> sp2 <= APPMEM_END ->
  ~ (sp2 - K <= x < sp2) -> ~ (fr + d <= x < fr + d + n) -> outside (fp_w [c] FS) x ->
  outside (cmWc fr sp2 K d n c) x.
Proof.
  intros fr sp2 K d n c x Hap H0 H1 Hw Hb Hf. unfold cmWc. cbn [outside].
  split; [exact Hb|]. split; [exact Hw|]. apply fl_out_app; [exact Hf|]. cbn [outside]. split; [|exact I].
  apply acl_sh_out; [exact Hap | lia | lia].
Qed.

(* Every byte of the shadow of an application range [lo, hi) (lo 8-aligned) is shadow memory. *)
Lemma cm_sh_in : forall lo hi y, lo mod 8 = 0 -> (forall a, lo <= a < hi -> app_mem a) ->
  shadow_addr lo <= y < shadow_addr hi -> in_shadow y.
Proof.
  intros lo hi y Hm Hap Hy.
  assert (Ex : shadow_addr (8 * (y - ASAN_K)) = y) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
  assert (Hx : lo <= 8 * (y - ASAN_K) < hi) by (unfold shadow_addr in *; Z.div_mod_to_equations; lia).
  rewrite <- Ex. apply rt_app_shadow. apply Hap. exact Hx.
Qed.

(* Every byte the callee may write reads back after its return: so every byte readable before stays readable. *)
Lemma cm_Wc_rd : forall fr sp2 K d n c mc mc', (c <= 2)%nat -> munch (cmWc fr sp2 K d n c) mc mc' ->
  (forall y, fr + d <= y < fr + d + n -> exists b, mrd rsegs mc' (wa y) = Some b) ->
  stk rsegs mc' (sp2 - K) sp2 -> stk rsegs mc' FS (FS + FS_SIZE) -> shadow_rw mc' ->
  (forall a, sp2 - K <= a < sp2 -> app_mem a) -> (sp2 - K) mod 8 = 0 -> rd_mono mc mc'.
Proof.
  intros fr sp2 K d n c mc mc' Hc MU HB STw STf SR' Happ Hm8.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof (rd_of_stk mc' _ _ STf) as RF.
  apply (rd_mono_list _ mc mc' MU).
  unfold cmWc. constructor; [exact HB|]. constructor; [intros y Hy; exact (rd_of_stk mc' _ _ STw y Hy)|].
  apply Forall_app. split.
  - assert (F8 : fs_frame FS c 0 mod 8 = 0).
    { unfold fs_frame, fs_B. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat]; try lia; Z.div_mod_to_equations; lia. }
    assert (FA : forall a, fs_frame FS c 0 <= a < fs_frame FS c (fs_M c) -> app_mem a).
    { intros a Ha. apply FSapp. unfold fs_frame, fs_B, fs_M, FS_SIZE in *.
      destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; try lia. }
    cbn [fp_w flat_map fp_w1 app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]];
      cbn [fst snd]; intros y Hy.
    + apply RF. unfold fs_hint, FS_SIZE in *. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
    + apply RF. unfold fs_flag, fs_M, FS_SIZE in *. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
    + apply RF. unfold fs_frame, fs_B, fs_M, FS_SIZE in *. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
    + exact (proj2 (SR' y (cm_sh_in _ _ y F8 FA Hy))).
  - constructor; [|constructor]. cbn [fst snd]. intros y Hy. exact (proj2 (SR' y (cm_sh_in _ _ y Hm8 Happ Hy))).
Qed.

(* The class-c hint word and flag bytes read back after writes apart from them (fp_cls in mc), or from a callee's fp. *)
Lemma cm_cls_keep : forall c mc mc' W, fp_cls mc FS c -> munch W mc mc' ->
  (forall x, fs_hint FS c <= x < fs_hint FS c + 8 -> outside W x) ->
  (forall x, fs_flag FS c 0 <= x < fs_flag FS c 0 + fs_M c -> outside W x) ->
  (exists h', bytes_at rsegs mc' (fs_hint FS c) (le8 h')) /\
  (exists flags', bytes_at rsegs mc' (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
     Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags').
Proof.
  intros c mc mc' W (_ & h & flags & HH & HFl & HL & H01) MU O1 O2. split.
  - exists h. apply (fl_bytes W mc mc' _ _ HH MU). intros x Hx. rewrite length_le8 in Hx. apply O1. lia.
  - exists flags. split; [|split; [exact HL | exact H01]]. apply (fl_bytes W mc mc' _ _ HFl MU).
    intros x Hx. apply O2. lia.
Qed.

Lemma cm_cls_fp : forall c mc' TP lo hi W D, fp [c] mc' TP FS lo hi W D ->
  (exists h', bytes_at rsegs mc' (fs_hint FS c) (le8 h')) /\
  (exists flags', bytes_at rsegs mc' (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
     Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags').
Proof.
  intros c mc' TP lo hi W D (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & HCL & _).
  inversion HCL as [|? ? Hc' _]; subst. destruct Hc' as (_ & h & flags & HH & HFl & HL & H01).
  split; [exists h; exact HH | exists flags; split; [exact HFl | split; [exact HL | exact H01]]].
Qed.

(* A hint or flag byte of another class c' is apart from the callee writes of class c. *)
Lemma cm_cls_out_Wc : forall fr sp2 jj nn K d n c c' x, cmFK fr sp2 jj nn -> (c <= 2)%nat -> (c' <= 2)%nat ->
  c <> c' -> 0 <= K <= 8800 -> 0 <= d -> d + n <= 192 ->
  (fs_hint FS c' <= x < fs_hint FS c' + 8 \/ fs_flag FS c' 0 <= x < fs_flag FS c' 0 + fs_M c') ->
  outside (cmWc fr sp2 K d n c) x.
Proof.
  intros fr sp2 jj nn K d n c c' x FK Hc Hc' Hne HKr Hd Hdn Hx.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE, HIGHMEM_BEG, APPMEM_END in *.
  assert (Xr : FS <= x < FS + 36864)
    by (clear -Hx Hc' FSpos; unfold fs_hint, fs_flag, fs_M in Hx;
        destruct c' as [|[|[|c']]]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia).
  assert (Hap : app_mem x) by (apply FSapp; clear -Xr; lia).
  apply cm_Wc_out; [exact Hap | clear -Gsp HKr HHM'; lia | clear -Gsp HAE'; unfold APPMEM_END; lia
                   | clear -Gsp HKr Xr FShi; lia | clear -Gfs Hd Xr; lia |].
  apply cm_fpw1_out; [exact Hc | exact Hap | | | left; clear -Xr; unfold fs_frame; lia];
    clear -Hc Hc' Hne Hx Xr FSpos; unfold fs_hint, fs_flag, fs_M in *;
    destruct c as [|[|[|c]]]; destruct c' as [|[|[|c']]]; cbn [Z.of_nat Pos.of_succ_nat] in *; try lia; congruence.
Qed.

(* The 12 saves [S - 96, S) are apart from the callee writes. *)
Lemma cm_Wc_saves : forall fr sp2 jj nn K d n c x, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] -> 0 <= K <= 8800 ->
  0 <= d -> d + n <= 192 -> S - 96 <= x < S -> outside (cmWc fr sp2 K d n c) x.
Proof.
  intros fr sp2 jj nn K d n c x FK Hc HKr Hd Hdn Hx.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE, HIGHMEM_BEG, APPMEM_END in *.
  assert (Hap : app_mem x) by (clear -Hx HHM' HAE'; unfold app_mem, HIGHMEM_BEG, APPMEM_END; lia).
  apply cm_Wc_out; [exact Hap | clear -Gsp HKr HHM'; lia | clear -Gsp HAE'; unfold APPMEM_END; lia
                   | clear -Gsp Hx; lia | clear -Gc Hdn Hd Hx; destruct Gc; lia |].
  apply (cm_out_fpw_c c x Hc). apply acl_out_fpw_hi; [clear -Hx FShi; unfold FS_SIZE; lia | exact Hap].
Qed.

(* The epilogue's flag-pointer word [fr + 248, fr + 256) (side path) is apart from the callee writes of class 0 or 1. *)
Lemma cm_Wc_flag : forall fr sp2 jj nn K d n c x, cmFK fr sp2 jj nn -> nn = 1 -> (c <= 1)%nat -> 0 <= K <= 8800 ->
  0 <= d -> d + n <= 192 -> fr + 248 <= x < fr + 256 -> outside (cmWc fr sp2 K d n c) x.
Proof.
  intros fr sp2 jj nn K d n c x FK En1 Hc HKr Hd Hdn Hx.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE, HIGHMEM_BEG, APPMEM_END in *.
  destruct Gc as [(En & _) | (En & Ef & Hj & Fhi & Fhi2)]; [clear -En En1; lia|].
  assert (Hap : app_mem x) by (apply FSapp; clear -Hx Fhi Ef Hj; unfold FS_SIZE; lia).
  apply cm_Wc_out; [exact Hap | clear -Gsp HKr HHM'; lia | clear -Gsp HAE'; unfold APPMEM_END; lia
                   | clear -Gsp HKr Hx Fhi2; lia | clear -Hx Hdn; lia |].
  apply cm_fpw1_out; [clear -Hc; lia | exact Hap | | | ]; right; clear -Hx Ef Hj Hc;
    unfold fs_hint, fs_flag, fs_M, fs_frame, fs_B; destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

(* An application range is apart from the shadow of an application range [lo, hi). *)
Lemma cm_dj_sh : forall a b lo hi, (forall z, a <= z < b -> app_mem z) -> a < b -> 0 <= lo -> lo < hi ->
  hi <= APPMEM_END -> ly_dj a b (shadow_addr lo) (shadow_addr hi).
Proof.
  intros a b lo hi Hap Hab Hlo Hlh Hhi. unfold ly_dj.
  destruct (Z_le_gt_dec b (shadow_addr lo)) as [L1|L1]; [left; exact L1|].
  destruct (Z_le_gt_dec (shadow_addr hi) a) as [L2|L2]; [right; exact L2|].
  exfalso. pose proof (Hap (Z.max a (shadow_addr lo)) ltac:(lia)) as Hz.
  clear Hap. unfold app_mem, shadow_addr, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

(* A buffer of the frame is apart from the class-0 and class-1 side-stack bytes. *)
Lemma cm_dj_buf : forall fr sp2 jj nn d n c, cmFK fr sp2 jj nn -> (c <= 1)%nat -> 0 <= d -> 0 < n -> d + n <= 192 ->
  fp_dj [(fr + d, fr + d + n)] (fp_w [c] FS).
Proof.
  intros fr sp2 jj nn d n c FK Hc Hd Hn Hdn.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & _ & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HAE as HAE'. unfold FS_SIZE in FShi.
  assert (Hfr : fs_frame FS c (fs_M c) <= fr).
  { clear -Gc Hc FShi Gsp. unfold fs_frame, fs_B, fs_M.
    destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; destruct Gc as [(_ & E & _)|(_ & E & Hj & _)]; lia. }
  unfold fp_dj. constructor; [|constructor]. cbn [fp_w flat_map fp_w1 app].
  constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [fst snd]; unfold ly_dj.
  - right. clear -Gfs Hd Hc. unfold fs_hint. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
  - right. clear -Gfs Hd Hc. unfold fs_flag, fs_M. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
  - right. clear -Hfr Hd. lia.
  - apply cm_dj_sh.
    + intros z Hz. replace z with (fr + (z - fr)) by (clear; lia). apply FAP. clear -Hz Hd Hdn. lia.
    + clear -Hn. lia.
    + clear -FSpos Hc. unfold fs_frame, fs_B. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
    + clear -Hc. unfold fs_frame, fs_B, fs_M. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
    + clear -Hc FShi HAE'. unfold fs_frame, fs_B, fs_M, APPMEM_END in *.
      destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

(* A range of the image below ASAN_GT is apart from the side-stack bytes of any class c <= 2. *)
Lemma cm_dj_lo : forall a b c, 0 <= a < b -> b <= ASAN_GT -> (c <= 2)%nat -> fp_dj [(a, b)] (fp_w [c] FS).
Proof.
  intros a b c Hab Hb Hc. destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  clear -Hab Hb Hc FSpos FSgt.
  unfold fp_dj. constructor; [|constructor]. cbn [fp_w flat_map fp_w1 app].
  constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [fst snd]; unfold ly_dj; left;
    unfold fs_hint, fs_flag, fs_frame, fs_B, fs_M, shadow_addr, ASAN_GT, ASAN_K in *;
    destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat]; try lia; Z.div_mod_to_equations; lia.
Qed.

(* The 50 input bytes at f are apart from the frame's 192 bytes. *)
Lemma cm_f_apart : 50 <= len -> forall fr sp2 jj nn, cmFK fr sp2 jj nn -> fr + 192 <= f \/ f + 50 <= fr.
Proof.
  intros HL fr sp2 jj nn FK. destruct (HF HL) as (Hf0 & Hf50 & _ & Hdj).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc). pose proof cm_fr2 as (F20 & F2M).
  destruct Gc as [(En & Ef & Fhi) | (En & Ef & Hj & Fhi & Fhi2)]; [clear -Hdj Ef Fhi Gsp; lia|].
  destruct acl_fs as (_ & _ & _ & _ & _ & DJ). unfold fp_dj, aDf in DJ.
  replace (len <? 50) with false in DJ by (symmetry; apply Z.ltb_ge; exact HL).
  apply Forall_cons_iff in DJ as [D1 _]. rewrite Forall_forall in D1.
  pose proof (D1 _ (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as Hly. cbn [fst snd] in Hly. rewrite F20, F2M in Hly.
  unfold ly_dj in Hly. clear -Hly Ef Fhi Hj. lia.
Qed.

(* The shadow byte of a window byte outside the callee window [sp2 - 8800, sp2) is apart from the callee writes. *)
Lemma cm_Wc_sh_out : forall fr sp2 jj nn K d n c x, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] ->
  0 <= K <= 8800 -> K mod 8 = 0 -> 0 <= d -> d + n <= 192 -> S - 9136 <= x < S ->
  ~ (sp2 - 8800 <= x < sp2) -> outside (cmWc fr sp2 K d n c) (shadow_addr x).
Proof.
  intros fr sp2 jj nn K d n c x FK Hc HKr HK8 Hd Hdn Hx Hx2.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE in FShi. unfold HIGHMEM_BEG in HHM'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem x) by (clear -Hx HHM' HAE'; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
  pose proof (rt_app_shadow x Hap) as Hsh.
  assert (Ho3 : outside (fp_w [0%nat; 1%nat; 2%nat] FS) x)
    by (apply acl_out_fpw_hi; [clear -Hx FShi; unfold FS_SIZE; lia | exact Hap]).
  unfold cmWc. cbn [outside]. split; [|split].
  - apply (sh_out_app _ (fr + d) (fr + d + n) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by (clear -Hz; lia). apply FAP. clear -Hz Hd Hdn. lia.
  - apply (sh_out_app _ (sp2 - K) sp2 Hsh).
    intros z Hz. clear -Hz Gsp HKr HHM' HAE'. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply fl_out_app; [exact (cm_out_fpw_c c (shadow_addr x) Hc (acl_out_fpw_sh x Hap Ho3))|].
    cbn [outside]. split; [|exact I].
    apply acl_win_sh; [clear -G16 HK8; Z.div_mod_to_equations; lia | clear -Hx2 HKr; lia].
Qed.

(* The invariant survives a call whose writes Wm are inside aWc and apart from the saves and the flag word, given the
   class hint/flag readback, the callee window addressable and every readable byte still readable. *)
Lemma cm_inv_mu : forall fr sp2 jj nn mc mc' Wm,
  cmInv fr sp2 jj nn mc ->
  munch Wm mc mc' -> wmono rsegs mc mc' -> rd_mono mc mc' -> mem_inv rsegs mc' ->
  sub_fp Wm aWc ->
  (forall c, In c [0%nat; 1%nat; 2%nat] ->
     (exists h', bytes_at rsegs mc' (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs mc' (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  addressable mc' (sp2 - 8800) 8800 ->
  (forall x, S - 9136 <= x < S -> ~ (fr <= x < fr + 192) -> ~ (sp2 - 8800 <= x < sp2) ->
     outside Wm (shadow_addr x)) ->
  (forall x, S - 96 <= x < S -> outside Wm x) ->
  (nn = 1 -> forall x, fr + 248 <= x < fr + 256 -> outside Wm x) ->
  cmInv fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' Wm INV MU WM RM MI' SUB Hcls AD' OAW OSV OFL.
  destruct INV as (FK & MUmc & WMmc & RMmc & MImc & ACmc & SRmc & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof FPg as FPpack.
  destruct FPg as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTPle & HPl & H88 & H96 & HCL & HFSlo & HApphi & HWd & HDd).
  destruct HPl as (HP1 & HP2 & HP3 & HP4 & HPstk).
  split; [exact FK|].
  split; [exact (munch_trans aWc m mc mc' MUmc (munch_weaken Wm aWc mc mc' SUB MU))|].
  split; [exact (wmono_trans rsegs m mc mc' WMmc WM)|].
  split; [exact (rd_mono_trans m mc mc' RMmc RM)|].
  split; [exact MI'|].
  split; [exact (fl_asan_cells Wm mc mc' ACmc MU (fun x Hx => SUB x (acl_rt_out_Wc x Hx)))|].
  split; [exact (shadow_rw_mono mc mc' SRmc WM RM)|].
  split.
  { apply (fl_fp_free [0%nat; 1%nat; 2%nat] mc mc' (bv_unsigned tp) FS (S - 9136) S aWf aDf Wm FPpack TLg MU WM).
    - unfold aWf, aWc, aXs in *. cbn [app]. exact SUB.
    - intros x Hx. apply SUB. exact (acl_hdr_out_Wc x Hx).
    - intros x Hx. right. apply RM. exact (rd_of_stk mc FS (FS + FS_SIZE) HPstk x Hx).
    - exact Hcls. }
  split.
  { intros DT TS C T DB kk HTcells'.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUB. unfold aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLg DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same mc mc' Wm (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells' MU Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLg DT TS C T DB kk HT0). }
  split; [exact AD'|].
  split.
  { intros x Hx Hxf.
    destruct (Z_lt_le_dec x (sp2 - 8800)) as [Lo|Lo].
    - exact (cm_ab_keep Wm mc mc' x (AWXg x Hx Hxf) MU (OAW x Hx Hxf ltac:(clear -Lo; lia))).
    - destruct (Z_lt_le_dec x sp2) as [In2|Hi2].
      + pose proof AD' as AD'c. destruct AD'c as (_ & _ & _ & ADb).
        pose proof (ADb (x - (sp2 - 8800)) ltac:(clear -Lo In2; lia)) as ABx.
        replace (sp2 - 8800 + (x - (sp2 - 8800))) with x in ABx by (clear; lia). exact ABx.
      + exact (cm_ab_keep Wm mc mc' x (AWXg x Hx Hxf) MU (OAW x Hx Hxf ltac:(clear -Hi2; lia))). }
  split.
  { apply (acl_rw Wm mc mc' (S - 96) cmSAVES SVg MU WM).
    intros x Hx. apply OSV. unfold cmSAVES in Hx. cbn [cells_size csize] in Hx. clear -Hx. lia. }
  intros Enn.
  apply (fl_bytes Wm mc mc' (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) (FLg Enn) MU).
  intros x Hx. rewrite length_le8 in Hx. apply (OFL Enn). clear -Hx. lia.
Qed.

(* The register state at the 11-row loop head (pc 0x846ac), row i: s0 = S, s1 = CA, s2 = frame, s3 = the row
   address T + 296 i, s4 = fr + 112 (the model buffer), s5 = f + 18 (the input's 32 bytes), s6 = shadow_addr fr,
   s7 = fr, s8 = 11 - i (the rows left), s9 = 1, s10 = -8; the gate passed and no earlier row matches. *)
Definition cmLH (i : nat) (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).

(* The register state at the no-row tail (pc 0x84700): the parse result other than 9 and the exhausted loop reach it
   with the invariant at mc, and there the result the contract names is 0 (want CM_T len fb = 0). *)
Definition cmNone (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = 0 -> cmInv fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) rs3 rs4 rs5 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84700) fc None mc (seg_rom rsegs)).

(* The run from the reac_ctrl_parse call at 0x84684 to the loop head: the call runs by its asan contract at the frame
   buffer [fr + 32, fr + 68) with the side-stack footprint fp [1] (fp_single of the invariant's fp [0;1;2]); at its
   return the invariant is rebuilt at the written memory (cm_inv_mu), `bne a0,9` sends a result other than 9 to the
   no-row tail (cmNone), and the equal branch sets up the loop registers and reaches the loop head of row 0. *)
Lemma cm_parse : forall Q, cmLH 0 Q -> cmNone Q -> cmPB Q.
Proof.
  intros Q KL KN fr sp2 jj nn mc rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 L E12 E13 E16 E17 INV APB.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  pose proof (cm_FB mc L MUg) as BF. pose proof (cm_AF mc L MUg) as AF.
  pose proof (cm_stk_win fr sp2 jj nn mc INVk) as STW.
  destruct (stk_split rsegs mc (S - 9136) (sp2 - 8800) S STW ltac:(clear -Gsp; lia)) as (_ & STW2).
  destruct (stk_split rsegs mc (sp2 - 8800) sp2 S STW2 ltac:(clear -Gsp; lia)) as (STc & _).
  pose proof (cm_stk_fr fr sp2 jj nn mc INVk) as STF.
  destruct (stk_split rsegs mc fr (fr + 68) (fr + 192) STF ltac:(clear -FRpos; lia)) as (STF2 & _).
  destruct (stk_carve rsegs mc fr (fr + 68) 36 STF2 ltac:(clear -FRpos; lia)) as (_ & (junk & RWo)).
  replace (fr + 68 - Z.of_nat 36) with (fr + 32) in RWo by (clear -FRpos; lia).
  pose proof (cm_f_apart L fr sp2 jj nn FK) as Hfo.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  clear STW STW2 STF STF2.
  step.
  eapply evt_cut.
  { eapply HPC with (f := f) (n := len) (o := fr + 32) (S := sp2) (FS := FS) (fr := fb) (junk := junk);
      unfold REAC_CTRL_PARSE_K.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Rf.
    - exact Rlen.
    - clear -FRpos FRhi RS. lia.
    - clear -Gsp RS. lia.
    - exact G16.
    - clear -Gsp HK. lia.
    - exact STc.
    - exact MIg.
    - exact Hfb.
    - intros _. split; [exact Hf0|]. split; [exact Hf50|]. clear -Hfd Gsp. lia.
    - intros i Hi. apply (proj2 (proj2 BF)). rewrite Hfb. pose proof (cp_rd_lt39 len fb i Hi). clear -H. lia.
    - intros _. split; [clear -G8; Z.div_mod_to_equations; lia|]. split; [clear -FRhi RS; lia|].
      split; [exact RWo|]. split; [clear -Gc Gsp; destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia|].
      intros _. clear -Hfo. lia.
    - exact ACg.
    - exact SRg.
    - clear -Gsp HHM. lia.
    - clear -Gsp HAE. lia.
    - exact ADg.
    - intros _. exact AF.
    - intros _. split; [exact APB|].
      split; [replace (fr + 32 + 36) with (fr + 68) by (clear -FRpos; lia); apply FAP; clear; lia|].
      right. clear -FRgt. unfold asan_stack_malloc_c.CF, ASAN_GT in *. lia.
    - apply (cm_lo_addr mc _ _ MUg ABC). unfold REAC_CTRL_PARSE_BC, ASAN_GT. lia.
    - apply (cm_lo_bytes mc _ _ MUg HBCMP); unfold REAL_BCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HMEMCMP); unfold REAL_MEMCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HGOT); unfold GOT_CF, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HCF254); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - apply (cm_lo_bytes mc _ _ MUg HCF255); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - unfold reac_ctrl_parse_W, reac_ctrl_parse_D, REAC_CTRL_PARSE_K.
      replace (fr + 32 =? 0) with false by (symmetry; apply Z.eqb_neq; clear -FRpos; lia).
      replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; exact L).
      cbn [app].
      apply (cm_fp_call 1%nat fr sp2 jj nn mc 8800 32 36); try (clear; lia).
      + exact INVk.
      + cbn. tauto.
      + apply (fl_dj_cons (f, f + 50) [(fr + 32, fr + 32 + 36)] (fp_w [1%nat] FS)). split.
        * unfold aDf in FSdj. replace (len <? 50) with false in FSdj by (symmetry; apply Z.ltb_ge; exact L).
          exact (fp_dj_incl _ _ _ (fp_w_incl 1%nat [0%nat; 1%nat; 2%nat] FS ltac:(cbn; tauto)) FSdj).
        * exact (cm_dj_buf fr sp2 jj nn 32 36 1%nat FK ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                   ltac:(clear; lia)).
    - unfold reac_ctrl_parse_tls, REAC_CTRL_PARSE_K.
      exact (cm_tls_call mc 1%nat 8800 sp2 TLg ltac:(cbn; tauto) ltac:(clear -Gsp; lia) ltac:(clear -Gsp; lia)). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E2 & MU2 & WM2
              & MI2 & ST2 & RO2 & AC2 & SW2 & AW2 & FP2 & TL2).
  subst ms'.
  specialize (RO2 ltac:(clear -FRpos; lia)).
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MU2, ST2, AW2.
  replace (fr + 32 =? 0) with false in MU2 by (symmetry; apply Z.eqb_neq; clear -FRpos; lia).
  cbn [app] in MU2.
  assert (MUc : munch (cmWc fr sp2 8800 32 36 1%nat) mc m2) by exact MU2. clear MU2.
  destruct (cm_bytes_of_rw rsegs m2 (fr + 32) 36 _ RO2) as (BO2 & LO2).
  assert (RDB : forall y, fr + 32 <= y < fr + 32 + 36 -> exists b, mrd rsegs m2 (wa y) = Some b).
  { intros y Hy. apply (acl_bytes_rd m2 (fr + 32) _ y BO2). rewrite LO2.
    change (Z.of_nat 36) with 36. clear -Hy. lia. }
  pose proof FP2 as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & (_ & _ & _ & _ & STFS2) & _).
  assert (APPw : forall a, sp2 - 8800 <= a < sp2 -> app_mem a).
  { intros a Ha. replace a with (sp2 - 8800 + (a - (sp2 - 8800))) by (clear -Ha; lia).
    apply (acl_app_in mc (sp2 - 8800) 8800); [exact ADg | clear -Ha; lia]. }
  assert (RM2 : rd_mono mc m2).
  { apply (cm_Wc_rd fr sp2 8800 32 36 1%nat mc m2 ltac:(clear; lia) MUc RDB ST2 STFS2 SW2 APPw
             ltac:(clear -G16; Z.div_mod_to_equations; lia)). }
  pose proof FPg as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (INV2 : cmInv fr sp2 jj nn m2).
  { apply (cm_inv_mu fr sp2 jj nn mc m2 (cmWc fr sp2 8800 32 36 1%nat) INVk MUc WM2 RM2 MI2).
    - exact (cm_Wc_sub fr sp2 jj nn 8800 32 36 1%nat FK ltac:(cbn; tauto) ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia) ltac:(clear; lia)).
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      + apply (cm_cls_keep 0%nat mc m2 (cmWc fr sp2 8800 32 36 1%nat) (HCL0 0%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 0%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 0%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
      + exact (cm_cls_fp 1%nat m2 (bv_unsigned tp) (sp2 - 8800) sp2 _ _ FP2).
      + apply (cm_cls_keep 2%nat mc m2 (cmWc fr sp2 8800 32 36 1%nat) (HCL0 2%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
    - exact AW2.
    - intros x Hx _ Hx2.
      exact (cm_Wc_sh_out fr sp2 jj nn 8800 32 36 1%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
               ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hx Hx2).
    - intros x Hx. exact (cm_Wc_saves fr sp2 jj nn 8800 32 36 1%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
                            ltac:(clear; lia) ltac:(clear; lia) Hx).
    - intros Enn x Hx. exact (cm_Wc_flag fr sp2 jj nn 8800 32 36 1%nat x FK Enn ltac:(clear; lia)
                                ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) Hx). }
  replace (ret_pc (Z_to_bv 64 0x84688)) with (Z_to_bv 64 0x84688)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step. step.
  pose proof (ctrlparse_kind_range len fb) as KR.
  rewrite cm_eqb_lit by (clear -KR; lia).
  destruct (Z.eqb_spec (fst (ctrlparse len fb)) 9) as [K9|K9]; cbn [negb]; cbv iota.
  - assert (G : RcMatch.cm_gate len fb = true).
    { unfold RcMatch.cm_gate. rewrite (proj2 (Z.leb_le 50 len) L), E12, E13, E16, E17, K9. reflexivity. }
    do 7 step.
    eapply KL; [exact G | intros j Hj; clear -Hj; lia | exact INV2].
  - eapply KN; [| exact INV2].
    apply cm_gate_false. unfold RcMatch.cm_gate. rewrite (proj2 (Z.eqb_neq _ _) K9).
    rewrite !andb_false_r. reflexivity.
Qed.

(* ---- the reac_box_model_block call and the 11-row loop ---- *)

(* After the un-poisoning stores (shadow bytes 14..17 -> 0), the model buffer [fr + 112, fr + 144) is addressable. *)
Lemma cm_model_addr : forall (mc0 : word -> option byte) (fr0 : Z),
  fr0 mod 8 = 0 -> 0 <= fr0 -> fr0 + 144 <= APPMEM_END ->
  (forall i, 0 <= i < 32 -> app_mem (fr0 + 112 + i)) ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 14) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 15) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 16) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 17) [Z_to_bv 8 0] ->
  addressable mc0 (fr0 + 112) 32.
Proof.
  intros mc0 fr0 Hm Hfr Hhi Hap B14 B15 B16 B17.
  assert (D : forall A v, bytes_at rsegs mc0 A [v] -> mrd rsegs mc0 (wa A) = Some v).
  { intros A v (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as HH. cbn in HH.
    rewrite Z.add_0_r in HH. exact HH. }
  pose proof (D _ _ B14) as R14. pose proof (D _ _ B15) as R15. pose proof (D _ _ B16) as R16.
  pose proof (D _ _ B17) as R17.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
  intros i Hi. split; [apply Hap; exact Hi|].
  destruct (Z_lt_le_dec i 8) as [c0|c0];
    [| destruct (Z_lt_le_dec i 16) as [c1|c1]; [| destruct (Z_lt_le_dec i 24) as [c2|c2]]].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 112 + i)) with (shadow_addr fr0 + 14)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R14
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 112 + i)) with (shadow_addr fr0 + 15)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R15
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 112 + i)) with (shadow_addr fr0 + 16)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R16
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 112 + i)) with (shadow_addr fr0 + 17)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R17
      | unfold shadow_ok; left; vm_compute; reflexivity ].
Qed.

(* reac_box_model_block's munch list (window first) is inside cmWc (buffer first). *)
Lemma cm_Wc_swap : forall fr sp2 K d n c,
  sub_fp ((sp2 - K, sp2) :: (fr + d, fr + d + n) :: fp_w [c] FS ++ [(shadow_addr (sp2 - K), shadow_addr sp2)])
         (cmWc fr sp2 K d n c).
Proof. intros fr sp2 K d n c x Hx. unfold cmWc in Hx. cbn [outside] in *. tauto. Qed.

(* The shadow byte of a window byte below the callee window [sp2 - K, sp2) is apart from the callee writes. *)
Lemma cm_Wc_sh_lo : forall fr sp2 jj nn K d n c x, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] ->
  0 <= K <= 8800 -> K mod 8 = 0 -> 0 <= d -> d + n <= 192 -> S - 9136 <= x < sp2 - K ->
  outside (cmWc fr sp2 K d n c) (shadow_addr x).
Proof.
  intros fr sp2 jj nn K d n c x FK Hc HKr HK8 Hd Hdn Hx.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE in FShi. unfold HIGHMEM_BEG in HHM'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem x) by (clear -Hx Gsp HKr HHM' HAE'; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
  pose proof (rt_app_shadow x Hap) as Hsh.
  assert (Ho3 : outside (fp_w [0%nat; 1%nat; 2%nat] FS) x)
    by (apply acl_out_fpw_hi; [clear -Hx FShi; unfold FS_SIZE; lia | exact Hap]).
  unfold cmWc. cbn [outside]. split; [|split].
  - apply (sh_out_app _ (fr + d) (fr + d + n) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by (clear -Hz; lia). apply FAP. clear -Hz Hd Hdn. lia.
  - apply (sh_out_app _ (sp2 - K) sp2 Hsh).
    intros z Hz. clear -Hz Gsp HKr HHM' HAE'. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply fl_out_app; [exact (cm_out_fpw_c c (shadow_addr x) Hc (acl_out_fpw_sh x Hap Ho3))|].
    cbn [outside]. split; [|exact I].
    apply acl_win_sh; [clear -G16 HK8; Z.div_mod_to_equations; lia | clear -Hx; lia].
Qed.

(* The callee window [sp2 - 8800, sp2) stays addressable: the part below the callee's window by its shadow apart from
   the callee writes, the callee's window by the callee's post. *)
Lemma cm_ad_join : forall fr sp2 jj nn K d n c ma mb, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] ->
  0 <= K <= 8800 -> K mod 8 = 0 -> 0 <= d -> d + n <= 192 ->
  addressable ma (sp2 - 8800) 8800 -> munch (cmWc fr sp2 K d n c) ma mb -> addressable mb (sp2 - K) K ->
  addressable mb (sp2 - 8800) 8800.
Proof.
  intros fr0 sp0 jj0 nn0 K d n c ma mb FK Hc HKr HK8 Hd Hdn ADa MU ADb.
  pose proof (cm_geo fr0 sp0 jj0 nn0 FK) as (_ & _ & G16' & Gsp' & _).
  assert (ADlo : addressable mb (sp0 - 8800) (8800 - K)).
  { apply (acl_addr_munch (cmWc fr0 sp0 K d n c) ma mb (sp0 - 8800) (8800 - K)
             (acl_addr_sub ma (sp0 - 8800) 8800 (sp0 - 8800) (8800 - K) ADa ltac:(clear; lia)
                ltac:(clear -HKr; lia) ltac:(clear -HKr; lia)) MU).
    intros k Hk. apply (cm_Wc_sh_lo fr0 sp0 jj0 nn0 K d n c _ FK Hc HKr HK8 Hd Hdn). clear -Hk Gsp' HKr. lia. }
  assert (AJ : addressable mb (sp0 - 8800) ((8800 - K) + K)).
  { apply (acl_addr_join mb (sp0 - 8800) (8800 - K) K ADlo); [| clear -HKr; lia].
    replace (sp0 - 8800 + (8800 - K)) with (sp0 - K) by (clear; lia). exact ADb. }
  replace (8800 - K + K) with 8800 in AJ by (clear; lia). exact AJ.
Qed.

(* The shadow byte of a byte of a frame buffer is apart from the writes of a class-0 or class-1 callee. *)
Lemma cm_Wc_sh_buf : forall fr sp2 jj nn K d n c k, cmFK fr sp2 jj nn -> (c <= 1)%nat -> 0 <= K <= 8800 ->
  K mod 8 = 0 -> 0 <= d -> d + n <= 192 -> 0 <= k < n ->
  outside (cmWc fr sp2 K d n c) (shadow_addr (fr + d + k)).
Proof.
  intros fr sp2 jj nn K d n c k FK Hc HKr HK8 Hd Hdn Hk.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE in FShi. unfold HIGHMEM_BEG in HHM'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem (fr + d + k)).
  { replace (fr + d + k) with (fr + (d + k)) by (clear; lia). apply FAP. clear -Hd Hdn Hk. lia. }
  pose proof (rt_app_shadow _ Hap) as Hsh.
  assert (Hfr0 : fs_frame FS c (fs_M c) <= fr).
  { clear -Gc Hc FShi Gsp. unfold fs_frame, fs_B, fs_M.
    destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; destruct Gc as [(_ & E & _)|(_ & E & Hj & _)]; lia. }
  unfold cmWc. cbn [outside]. split; [|split].
  - apply (sh_out_app _ (fr + d) (fr + d + n) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by (clear -Hz; lia). apply FAP. clear -Hz Hd Hdn. lia.
  - apply (sh_out_app _ (sp2 - K) sp2 Hsh).
    intros z Hz. clear -Hz Gsp HKr HHM' HAE'. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply fl_out_app.
    + cbn [fp_w flat_map fp_w1 app outside]. split; [|split; [|split; [|split; [|exact I]]]].
      * apply (sh_out_app _ (fs_hint FS c) (fs_hint FS c + 8) Hsh). intros z Hz. apply FSapp.
        clear -Hz Hc FSpos. unfold fs_hint, FS_SIZE in *. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
      * apply (sh_out_app _ (fs_flag FS c 0) (fs_flag FS c 0 + fs_M c) Hsh). intros z Hz. apply FSapp.
        clear -Hz Hc FSpos. unfold fs_flag, fs_M, FS_SIZE in *.
        destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
      * apply (sh_out_app _ (fs_frame FS c 0) (fs_frame FS c (fs_M c)) Hsh). intros z Hz. apply FSapp.
        clear -Hz Hc FSpos. unfold fs_frame, fs_B, fs_M, FS_SIZE in *.
        destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
      * apply acl_win_sh;
          [ clear -Hc FSmod; unfold fs_frame, fs_B; destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat];
            Z.div_mod_to_equations; lia
          | clear -Hfr0 Hd Hk; lia ].
    + cbn [outside]. split; [|exact I].
      apply acl_win_sh; [clear -G16 HK8; Z.div_mod_to_equations; lia |].
      clear -Gc Gsp HKr Hd Hdn Hk FShi.
      destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia.
Qed.

(* The register state at the row-match tail (pc 0x84864): the bcmp wrapper returned 0, s3 is the matching row's
   address r, and there the result the contract names is r (want CM_T len fb = r). *)
Definition cmHit (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn r : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = r -> cmInv fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) rs4 rs5
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84864) fc None mc (seg_rom rsegs)).

(* The register state at the bcmp wrapper call (pc 0x846dc), row i: a0 = f + 18, a1 = fr + 112, a2 = 32, the loop
   registers as at the loop head; the model buffer is addressable and holds row i's 32-byte declaration. *)
Definition cmBC (i : nat) (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (i < 11)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
    bytes_at rsegs mc (fr + 112) (nth i DECLS []) ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 32) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846dc) fc None mc (seg_rom rsegs)).

(* The run from the loop head at 0x846ac (row i) to the bcmp wrapper call: the un-poisoning of the model buffer's
   shadow (bytes 14..17 -> 0, inside cmHF fr, cm_inv_step), the reac_box_model_block call (row T + 296 i, b = 0,
   o = fr + 112) by its asan contract with the side-stack footprint fp [0] (fp_single); the row is a catalogue row, so
   the result is 1 and the buffer holds row i's declaration (cm_rc); at the return the invariant is rebuilt
   (cm_inv_mu), `bne a0,s9` (s9 = 1) falls through, and a0/a1/a2 are set for the bcmp wrapper (cmBC). *)
Lemma cm_model : forall i Q, (i < 11)%nat -> cmBC i Q -> cmLH i Q.
Proof.
  intros i Q Hi KB fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hnd INV.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  clear MUg.
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
    unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold cmHF in MUh.
  cm_wst (shadow_addr fr + 14) 1%nat. step. cm_keep B14.
  cm_wst (shadow_addr fr + 15) 1%nat. step. cm_keep B15.
  cm_wst (shadow_addr fr + 16) 1%nat. step. cm_keep B16.
  cm_wst (shadow_addr fr + 17) 1%nat. step. cm_keep B17.
  pose proof (cm_inv_step fr sp2 jj nn mc _ INVk MUh WMh RMh MIg) as INV1.
  pose proof INV1 as INV1k.
  destruct INV1 as (_ & MU1 & WM1 & RM1 & MI1 & AC1 & SR1 & FP1 & TL1 & AD1 & AWX1 & SV1 & FL1).
  assert (ADm : addressable m1 (fr + 112) 32).
  { apply (cm_model_addr m1 fr FR8 ltac:(clear -FRpos; lia)
             ltac:(clear -FRhi HAE; unfold APPMEM_END in *; lia));
      [ intros k Hk; replace (fr + 112 + k) with (fr + (112 + k)) by (clear -Hk; lia); apply FAP; clear -Hk; lia
      | exact B14 | exact B15 | exact B16 | exact B17 ]. }
  pose proof (cm_stk_fr fr sp2 jj nn m1 INV1k) as STF1.
  destruct (stk_split rsegs m1 fr (fr + 144) (fr + 192) STF1 ltac:(clear -FRpos; lia)) as (STF1a & _).
  destruct (stk_carve rsegs m1 fr (fr + 144) 32 STF1a ltac:(clear -FRpos; lia)) as (_ & (ob & RWm)).
  replace (fr + 144 - Z.of_nat 32) with (fr + 112) in RWm by (clear -FRpos; lia).
  pose proof (cm_stk_win fr sp2 jj nn m1 INV1k) as STW1.
  destruct (stk_split rsegs m1 (S - 9136) (sp2 - 4272) S STW1 ltac:(clear -Gsp; lia)) as (_ & STW1b).
  destruct (stk_split rsegs m1 (sp2 - 4272) sp2 S STW1b ltac:(clear -Gsp; lia)) as (STc1 & _).
  pose proof (cm_tbl m1 MU1) as BT.
  pose proof (bytes_at_sub rsegs m1 CM_T CM_TBL (296 * i) 296 BT ltac:(rewrite CM_TBL_len; clear -Hi; lia)) as BR.
  apply (bytes_at_addr rsegs m1 _ (CM_T + 296 * Z.of_nat i)) in BR; [|clear; lia].
  fold (cm_row i) in BR.
  pose proof (cm_lo_addr m1 CM_T 3256 MU1 AT ltac:(unfold CM_T, ASAN_GT; clear; lia)) as ATm.
  do 4 step.
  eapply evt_cut.
  { eapply HMB with (p := CM_T + 296 * Z.of_nat i) (b := 0) (o := fr + 112) (FS := FS)
                    (row := cm_row i) (nb := @nil byte) (ob := ob);
      rewrite ?unsigned_lit by (clear -Gsp RS HK; lia); unfold REAC_BOX_MODEL_BLOCK_K.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold CM_T. clear -Hi. lia.
    - clear. lia.
    - clear -FRpos FRhi RS. lia.
    - exact G16.
    - exact STc1.
    - intros _. split; [unfold CM_T; clear -Hi; Z.div_mod_to_equations; lia|].
      split; [exact (cm_row_len i Hi)|]. split; [exact BR|].
      split; [right; unfold CM_T in *; clear -Hi Gsp HHM; unfold HIGHMEM_BEG in *; lia|].
      right; right; clear -Hi FRgt; unfold CM_T, ASAN_GT in *; lia.
    - intros _ [E|E]; discriminate E.
    - intros _. split; [exact RWm|].
      split; [clear -Gc Gsp FShi; destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia|].
      right. clear -FRgt. unfold JOIN_0014, ASAN_GT in *. lia.
    - exact MI1.
    - exact AC1.
    - exact SR1.
    - clear -Gsp HHM. unfold HIGHMEM_BEG in *. lia.
    - clear -Gsp HAE. lia.
    - exact (acl_addr_sub m1 (sp2 - 8800) 8800 (sp2 - 4272) 4272 AD1 ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia)).
    - intros _. exact (acl_addr_sub m1 CM_T 3256 (CM_T + 296 * Z.of_nat i) 296 ATm ltac:(clear -Hi; lia)
                         ltac:(clear; lia) ltac:(clear -Hi; lia)).
    - intros _ [E|E]; discriminate E.
    - intros _. split; [exact ADm|].
      split; [replace (fr + 112 + 32) with (fr + 144) by (clear; lia); apply FAP; clear; lia|].
      right. clear -FRgt. unfold RT_HI, ASAN_GT in *. lia.
    - intros E; discriminate E.
    - intros E; discriminate E.
    - unfold reac_box_model_block_W, reac_box_model_block_D.
      replace (fr + 112 =? 0) with false by (symmetry; apply Z.eqb_neq; clear -FRpos; lia).
      replace (CM_T + 296 * Z.of_nat i =? 0) with false
        by (symmetry; apply Z.eqb_neq; unfold CM_T; clear -Hi; lia).
      cbn [app].
      apply (cm_fp_call 0%nat fr sp2 jj nn m1 4272 112 32); try (clear; lia).
      + exact INV1k.
      + cbn. tauto.
      + apply (fl_dj_cons (CM_T + 296 * Z.of_nat i, CM_T + 296 * Z.of_nat i + 296)
                 [(fr + 112, fr + 112 + 32)] (fp_w [0%nat] FS)). split.
        * apply cm_dj_lo; [unfold CM_T; clear -Hi; lia | unfold CM_T, ASAN_GT; clear -Hi; lia | clear; lia].
        * exact (cm_dj_buf fr sp2 jj nn 112 32 0%nat FK ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                   ltac:(clear; lia)).
    - intros _ [E|E]; discriminate E.
    - unfold reac_box_model_block_tls.
      exact (cm_tls_call m1 0%nat 4272 sp2 TL1 ltac:(cbn; tauto) ltac:(clear -Gsp; lia) ltac:(clear -Gsp; lia)). }
  intros ms' Hpost. unfold reac_box_model_block_post in Hpost.
  rewrite (unsigned_lit sp2) in Hpost by (clear -Gsp RS HK; lia).
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                     & m2 & E2 & PB & WM2 & MI2 & ST2 & AC2 & SW2 & AW2 & FP2 & TL2).
  subst ms'.
  assert (Z0 : (CM_T + 296 * Z.of_nat i =? 0) || (fr + 112 =? 0) = false)
    by (apply orb_false_iff; split; apply Z.eqb_neq; [unfold CM_T; clear -Hi; lia | clear -FRpos; lia]).
  rewrite Z0 in PB |- *. destruct PB as (BB & MU2).
  destruct (cm_rc i (@nil byte) Hi) as (RC & SY). rewrite RC. rewrite SY in BB.
  unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in MU2, ST2, AW2. cbn [app] in MU2.
  assert (MUc : munch (cmWc fr sp2 4272 112 32 0%nat) m1 m2)
    by exact (munch_weaken _ _ m1 m2 (cm_Wc_swap fr sp2 4272 112 32 0%nat) MU2).
  clear MU2.
  pose proof (cm_decl_len i Hi) as LD.
  assert (RDB : forall y, fr + 112 <= y < fr + 112 + 32 -> exists b, mrd rsegs m2 (wa y) = Some b).
  { intros y Hy. apply (acl_bytes_rd m2 (fr + 112) _ y BB). rewrite LD.
    change (Z.of_nat 32) with 32. clear -Hy. lia. }
  pose proof FP2 as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & (_ & _ & _ & _ & STFS2) & _).
  assert (APPw : forall a, sp2 - 4272 <= a < sp2 -> app_mem a).
  { intros a Ha. replace a with (sp2 - 8800 + (a - (sp2 - 8800))) by (clear -Ha; lia).
    apply (acl_app_in m1 (sp2 - 8800) 8800); [exact AD1 | clear -Ha; lia]. }
  assert (RM2 : rd_mono m1 m2).
  { apply (cm_Wc_rd fr sp2 4272 112 32 0%nat m1 m2 ltac:(clear; lia) MUc RDB ST2 STFS2 SW2 APPw
             ltac:(clear -G16; Z.div_mod_to_equations; lia)). }
  pose proof FP1 as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (AD2 : addressable m2 (sp2 - 8800) 8800)
    by exact (cm_ad_join fr sp2 jj nn 4272 112 32 0%nat m1 m2 FK ltac:(cbn; tauto) ltac:(clear; lia)
                ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) AD1 MUc AW2).
  assert (INV2 : cmInv fr sp2 jj nn m2).
  { apply (cm_inv_mu fr sp2 jj nn m1 m2 (cmWc fr sp2 4272 112 32 0%nat) INV1k MUc WM2 RM2 MI2).
    - exact (cm_Wc_sub fr sp2 jj nn 4272 112 32 0%nat FK ltac:(cbn; tauto) ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia) ltac:(clear; lia)).
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      + exact (cm_cls_fp 0%nat m2 (bv_unsigned tp) (sp2 - 4272) sp2 _ _ FP2).
      + apply (cm_cls_keep 1%nat m1 m2 (cmWc fr sp2 4272 112 32 0%nat) (HCL0 1%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 1%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 1%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
      + apply (cm_cls_keep 2%nat m1 m2 (cmWc fr sp2 4272 112 32 0%nat) (HCL0 2%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
    - exact AD2.
    - intros x Hx _ Hx2.
      exact (cm_Wc_sh_out fr sp2 jj nn 4272 112 32 0%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
               ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hx Hx2).
    - intros x Hx. exact (cm_Wc_saves fr sp2 jj nn 4272 112 32 0%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
                            ltac:(clear; lia) ltac:(clear; lia) Hx).
    - intros Enn x Hx. exact (cm_Wc_flag fr sp2 jj nn 4272 112 32 0%nat x FK Enn ltac:(clear; lia)
                                ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) Hx). }
  assert (ADm2 : addressable m2 (fr + 112) 32).
  { apply (acl_addr_munch (cmWc fr sp2 4272 112 32 0%nat) m1 m2 (fr + 112) 32 ADm MUc).
    intros k Hk. exact (cm_Wc_sh_buf fr sp2 jj nn 4272 112 32 0%nat k FK ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hk). }
  replace (ret_pc (Z_to_bv 64 0x846cc)) with (Z_to_bv 64 0x846cc)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step.
  rewrite cm_eqb_lit by (clear; lia).
  replace (1 =? 1) with true by reflexivity. cbn [negb]. cbv iota.
  do 3 step.
  eapply KB; [exact G | exact Hi | exact Hnd | exact INV2 | exact ADm2 | exact BB].
Qed.

(* cmLH with the row-address and rows-left registers given by equations (for the loop's back edge). *)
Lemma cm_lh_eq : forall i Q, cmLH i Q ->
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 w3 w8 : word),
    w3 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w8 = Z_to_bv 64 (11 - Z.of_nat i) ->
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) w3
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               w8 (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).
Proof.
  intros i Q K fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 w3 w8 -> ->.
  apply K.
Qed.

(* The run from the bcmp wrapper call at 0x846dc (row i) to the next loop head: the wrapper compares the input's 32
   bytes at f + 18 with the model buffer by its contract (both ranges addressable, the window [sp2 - 4560, sp2) below
   the frame); at its return the invariant is rebuilt (cm_inv_mu, the wrapper writes only its window); `beqz a0` sends
   a match to the row-match tail (cmHit, want = T + 296 i); otherwise the model buffer's shadow is marked unusable
   again (bytes 14..17 -> 0xf8, inside cmHF fr), s8 counts down, s3 moves to the next row, and `bnez s8` reaches the
   loop head of row i + 1 (cmLH) or, after the last row, the no-row tail (cmNone, want = 0). *)
Lemma cm_bcmp : forall i Q, (i < 11)%nat -> ((i + 1 < 11)%nat -> cmLH (i + 1)%nat Q) -> cmNone Q -> cmHit Q ->
  cmBC i Q.
Proof.
  intros i Q Hi KL KN KH fr sp2 jj nn mc rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G _ Hnd INV ADb BB.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj). unfold FS_SIZE in FShi.
  assert (L : 50 <= len).
  { destruct (Z.leb_spec 50 len) as [L|L]; [exact L|]. exfalso. unfold RcMatch.cm_gate in G.
    rewrite (proj2 (Z.leb_gt 50 len) L) in G. cbn [andb] in G. discriminate G. }
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd). destruct (AFU L) as (_ & Af50).
  pose proof (cm_FB mc L MUg) as BF. pose proof (cm_AF mc L MUg) as AF.
  pose proof (bytes_at_sub rsegs mc f fb 18 32 BF ltac:(rewrite Hfb; clear; lia)) as BK.
  apply (bytes_at_addr rsegs mc _ (f + 18)) in BK; [|clear; lia].
  fold (cm_blk fb) in BK.
  assert (LK : length (cm_blk fb) = 32%nat)
    by (unfold cm_blk; rewrite length_firstn, length_skipn, Hfb; clear; lia).
  destruct (memcmp_model_total (cm_blk fb) (nth i DECLS []) 32 ltac:(rewrite LK; clear; lia)
              ltac:(rewrite (cm_decl_len i Hi); clear; lia)) as [v Hv].
  pose proof (mm_spec 32 (cm_blk fb) (nth i DECLS []) v LK (cm_decl_len i Hi) Hv) as [MM VR].
  pose proof (cm_stk_win fr sp2 jj nn mc INVk) as STW.
  destruct (stk_split rsegs mc (S - 9136) (sp2 - 4560) S STW ltac:(clear -Gsp; lia)) as (_ & STW2).
  destruct (stk_split rsegs mc (sp2 - 4560) sp2 S STW2 ltac:(clear -Gsp; lia)) as (STc & _).
  clear STW STW2.
  step.
  eapply evt_cut.
  { eapply HBC with (ls := cm_blk fb) (rs := nth i DECLS []) (v := v) (lo := sp2 - 4560);
      cbv zeta; rewrite ?unsigned_lit by (clear -Hf0 Hf50 FRpos FRhi RS Gsp HK; lia); unfold BCMP_WRAP_K.
    - exact BK.
    - exact BB.
    - exact Hv.
    - exact MIg.
    - clear. lia.
    - exact (acl_addr_sub mc f 50 (f + 18) 32 AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    - exact ADb.
    - unfold end_in_app. right. replace (f + 18 + 32) with (f + 50) by (clear; lia). exact Af50.
    - unfold end_in_app. right. replace (fr + 112 + 32) with (fr + 144) by (clear; lia). apply FAP. clear; lia.
    - right. replace (f + 18 + 7) with (f + 25) by (clear; lia). exact (acl_app_in mc f 50 25 AF ltac:(clear; lia)).
    - right. replace (fr + 112 + 7) with (fr + 119) by (clear; lia). apply FAP. clear; lia.
    - clear -Hfd Gsp. lia.
    - clear -Gc Gsp. destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia.
    - exact STc.
    - clear. lia.
    - clear -Gsp HHM. unfold HIGHMEM_BEG in *. lia.
    - clear -Gsp HAE. lia.
    - exact ACg.
    - exact SRg.
    - apply (cm_lo_bytes mc _ _ MUg HBCMP); unfold REAL_BCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HMEMCMP); unfold REAL_MEMCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HGOT); unfold GOT_CF, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HCF254); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - apply (cm_lo_bytes mc _ _ MUg HCF255); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia. }
  intros ms' Hpost. unfold bcmp_wrap_post in Hpost.
  rewrite (unsigned_lit sp2) in Hpost by (clear -Gsp RS HK; lia).
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                     & m2 & E2 & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & _ & _).
  subst ms'. unfold BCMP_WRAP_K in MU2.
  assert (SUBb : sub_fp [(sp2 - 4560, sp2)] aWc).
  { intros x Hx. unfold aWc in Hx. cbn [outside] in Hx |- *. destruct Hx as (Hw & _).
    split; [clear -Hw Gsp; lia | exact I]. }
  assert (RM2 : rd_mono mc m2).
  { apply (rd_mono_list _ mc m2 MU2). constructor; [|constructor]. cbn [fst snd].
    intros y Hy. exact (rd_of_stk m2 _ _ ST2 y Hy). }
  pose proof FPg as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (OB : forall x, x < S - 9136 \/ S - 96 <= x -> outside [(sp2 - 4560, sp2)] x).
  { intros x Hx. cbn [outside]. split; [clear -Hx Gsp; lia | exact I]. }
  assert (INV2 : cmInv fr sp2 jj nn m2).
  { apply (cm_inv_mu fr sp2 jj nn mc m2 [(sp2 - 4560, sp2)] INVk MU2 WM2 RM2 MI2 SUBb).
    - intros c Hc. apply (cm_cls_keep c mc m2 _ (HCL0 c Hc) MU2).
      + intros x Hx. apply OB. left. clear -Hx Hc FShi FSpos. unfold fs_hint in Hx.
        destruct Hc as [<-|[<-|[<-|[]]]]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia.
      + intros x Hx. apply OB. left. clear -Hx Hc FShi FSpos. unfold fs_flag, fs_M in Hx.
        destruct Hc as [<-|[<-|[<-|[]]]]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia.
    - apply (addr_munch _ mc m2 (sp2 - 8800) 8800 ADg MU2). intros k Hk.
      apply (fl_shadow_out [(sp2 - 4560, sp2)] (sp2 - 4560) sp2);
        [intros x Hx; exact Hx | clear -Gsp HHM; unfold HIGHMEM_BEG in *; lia |].
      apply rt_app_shadow. exact (acl_app_in mc (sp2 - 8800) 8800 k ADg Hk).
    - intros x Hx _ _. apply (fl_shadow_out [(sp2 - 4560, sp2)] (sp2 - 4560) sp2);
        [intros y Hy; exact Hy | clear -Gsp HHM; unfold HIGHMEM_BEG in *; lia |].
      apply rt_app_shadow. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
      right. pose proof HHM as HHMb. pose proof HAE as HAEb.
      unfold HIGHMEM_BEG, APPMEM_END in HHMb, HAEb. clear -Hx HHMb HAEb. lia.
    - intros x Hx. apply OB. right. clear -Hx. lia.
    - intros Enn x Hx. apply OB. left. clear -Hx Gc Enn. destruct Gc as [(E & _)|(_ & _ & _ & _ & E)]; lia. }
  replace (ret_pc (Z_to_bv 64 0x846e0)) with (Z_to_bv 64 0x846e0)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step.
  rewrite cm_eqb0 by (clear -VR; lia).
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  - eapply KH; [| exact INV2].
    apply cm_want_hit; [exact G | exact Hi | symmetry; apply MM; exact V0 | exact Hnd].
  - assert (Hne : nth i DECLS [] <> cm_blk fb) by (intros Hq; apply V0; apply MM; symmetry; exact Hq).
    assert (SHlo : 0 <= shadow_addr fr).
    { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
      unfold ASAN_K. clear -D. lia. }
    assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
    { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
    assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
    clear FSW.
    pose proof INV2 as INV2k.
    destruct INV2 as (_ & MUa & WMa & _).
    clear MUa MUg MU2.
    assert (MUh : munch (cmHF fr) m2 m2) by apply munch_refl.
    assert (WMh : wmono rsegs m2 m2) by apply wmono_refl.
    assert (RMh : rd_mono m2 m2) by apply rd_mono_refl.
    unfold cmHF in MUh.
    cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
    pose proof (cm_inv_step fr sp2 jj nn m2 _ INV2k MUh WMh RMh MI2) as INV3.
    step. step. step.
    rewrite cm_eqb_lit by (clear -Hi; lia).
    destruct (Z.eqb_spec (11 - Z.of_nat i + -1) 0) as [K0|K0]; cbn [negb]; cbv iota.
    + eapply KN; [| exact INV3].
      apply cm_want_none. intros j Hj.
      destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; clear -K0 Hj Hji; lia].
    + assert (HS11 : (i + 1 < 11)%nat).
      { destruct (Nat.ltb_spec i 10) as [Hlt|Hge]; [clear -Hlt; lia|].
        exfalso. apply K0. replace i with 10%nat by (clear -Hge Hi; lia). vm_compute. reflexivity. }
      eapply (cm_lh_eq (i + 1)%nat Q (KL HS11));
        [ f_equal; clear; lia | f_equal; clear; lia | exact G | | exact INV3 ].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; clear -Hj Hji; lia].
Qed.

(* The whole run after the gate: by downward induction on the rows left, every loop head of a row i < 11 reaches Q
   (cm_model, then cm_bcmp, then the next row), so the reac_ctrl_parse call reaches Q (cm_parse). *)
Lemma cm_loop : forall Q, cmNone Q -> cmHit Q -> forall k i, (i + k = 11)%nat -> (i < 11)%nat -> cmLH i Q.
Proof.
  intros Q KN KH k. induction k as [|k IH]; intros i Hik Hi; [clear -Hik Hi; lia|].
  apply (cm_model i Q Hi). apply (cm_bcmp i Q Hi); [| exact KN | exact KH].
  intros Hs. apply (IH (i + 1)%nat); clear -Hik Hs; lia.
Qed.

Lemma cm_calls : forall Q, cmNone Q -> cmHit Q -> cmPB Q.
Proof. intros Q KN KH. apply cm_parse; [apply (cm_loop Q KN KH 11 0); clear; lia | exact KN]. Qed.


(* ============================ (e) the no-match join, the row-match tail and the exit ============================ *)

(* The contract's post: the result in a0, sp and the callee-saved registers restored, and the memory facts the
   caller is given (the writes inside the window, the class-0/1/2 side-stack bytes and the window's shadow). *)
Definition cmPost : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch ([(S - 9136, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - 9136), shadow_addr S)]) m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 9136) S /\
    asan_cells m' /\ shadow_rw m' /\ addressable m' (S - 9136) 9136 /\
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - 9136) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D f len) /\
    reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (S - 9136) S.

(* A shadow byte is writable, so a 1-byte store at it is allowed. *)
Lemma cm_sh_sok : forall mc a, shadow_rw mc -> in_shadow a -> store_ok rsegs mc (wa a) 1 = true.
Proof.
  intros mc a HS Ha. pose proof (rt_shadow_bound a Ha) as R.
  apply (wv_store_ok mc mc a 1);
    [ intros i Hi; replace (a + i) with a by lia; exact (proj1 (HS a Ha)) | apply wmono_refl | lia | lia ].
Qed.

Lemma cm_sh_div : forall fr d, fr mod 8 = 0 -> shadow_addr (fr + d) = shadow_addr fr + d / 8.
Proof. intros fr d Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma cm_wtm_cases : forall bs mm (a x : word),
  write_to_mem mm a bs x = mm x \/ exists v, write_to_mem mm a bs x = Some v.
Proof.
  induction bs as [|b bs IH]; intros m0 a x; cbn [write_to_mem]; [left; reflexivity|].
  destruct (IH (fun y => if bv_eqb y a then Some b else m0 y) (a + 1)%bv x) as [E|E]; [|right; exact E].
  rewrite E. destruct (bv_eqb x a); [right; eexists; reflexivity | left; reflexivity].
Qed.

Lemma cm_shadow_rw_write : forall mc a bs, shadow_rw mc -> shadow_rw (write_to_mem mc a bs).
Proof.
  intros mc a bs H x Hx. destruct (H x Hx) as [Hw (b & Hb)]. split; [apply wview_write_mono, Hw|].
  unfold mrd in *. destruct (cm_wtm_cases bs mc a (wa x)) as [E|[v E]]; rewrite E;
    [exists b; exact Hb | exists v; reflexivity].
Qed.

(* n readable bytes at A are some byte list. *)
Lemma cm_rd_list : forall mc n A, 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, mrd rsegs mc (wa (A + i)) = Some b) ->
  exists bs, length bs = n /\ bytes_at rsegs mc A bs.
Proof.
  induction n as [|n IH]; intros A HA HN H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
  - destruct (H 0 ltac:(lia)) as [b0 E0]. rewrite Z.add_0_r in E0.
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & (_ & _ & HB)).
    { intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply H. lia. }
    exists (b0 :: bs). split; [cbn; rewrite Hl; reflexivity|]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact E0.
    + cbn in Hi. rewrite <- (HB i ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* The byte at q of a list each of whose places in ks was overwritten by the one byte wl. *)
Lemma cm_nth_fold1 : forall (wl : list byte) ks q bs,
  length wl = 1%nat -> (q < length bs)%nat -> (forall k, In k ks -> (k < length bs)%nat) ->
  nth_error (fold_left (fun l k => upd_bytes l k wl) ks bs) q =
    (if in_dec Nat.eq_dec q ks then nth_error wl 0 else nth_error bs q).
Proof.
  intros wl ks. induction ks as [|k ks IH]; intros q bs Hw Hq Hk; cbn [fold_left].
  - reflexivity.
  - assert (Hkb : (k < length bs)%nat) by (apply Hk; left; reflexivity).
    assert (Hlen : length (upd_bytes bs k wl) = length bs) by (apply upd_bytes_length; lia).
    rewrite (IH q (upd_bytes bs k wl) Hw ltac:(rewrite Hlen; exact Hq)
               ltac:(intros k0 Hk0; rewrite Hlen; apply Hk; right; exact Hk0)).
    rewrite (upd_bytes_nth bs k wl q ltac:(lia) Hq).
    cbn [In].
    destruct (in_dec Nat.eq_dec q ks) as [Hin|Hnin].
    + destruct (in_dec Nat.eq_dec q (k :: ks)) as [_|Hnin']; [reflexivity|].
      exfalso; apply Hnin'; right; exact Hin.
    + destruct ((k <=? q)%nat && (q <? k + length wl)%nat)%bool eqn:Econd.
      * apply andb_true_iff in Econd. destruct Econd as [HA HB].
        apply Nat.leb_le in HA. apply Nat.ltb_lt in HB. rewrite Hw in HB.
        assert (Eqk : q = k) by lia. subst q. rewrite Nat.sub_diag.
        destruct (in_dec Nat.eq_dec k (k :: ks)) as [_|Hnin']; [reflexivity|].
        exfalso; apply Hnin'; left; reflexivity.
      * destruct (in_dec Nat.eq_dec q (k :: ks)) as [Hin'|_]; [|reflexivity].
        exfalso. destruct Hin' as [E|E]; [| contradiction].
        subst q. rewrite Nat.leb_refl in Econd. rewrite Hw in Econd. cbn [andb] in Econd.
        apply Nat.ltb_ge in Econd. lia.
Qed.

(* The order in which the exit sets the frame's 24 shadow bytes. *)
Definition cm_ks : list nat := [4;5;6;7;0;1;2;3;12;13;14;15;8;9;10;11;20;21;22;23;16;17;18;19]%nat.
Lemma cm_ks_bound : forall k, In k cm_ks -> (k < 24)%nat.
Proof. intros k Hk; unfold cm_ks in Hk; cbn [In] in Hk; decompose [or] Hk; subst; lia. Qed.
Lemma cm_ks_cover : forall q, (q < 24)%nat -> In q cm_ks.
Proof.
  intros q Hq; unfold cm_ks.
  do 24 (destruct q as [|q]; [cbn [In]; repeat (first [left; reflexivity | right])|]). lia.
Qed.

(* A range [a, b) inside a range of X: every range of T that is apart from X is apart from [a, b). *)
Lemma cm_dj_in : forall T X a' b' a b, fp_dj T X -> In (a', b') X -> a' <= a -> b <= b' ->
  Forall (fun d => ly_dj a b (fst d) (snd d)) T.
Proof.
  intros T X a' b' a b H Hin H1 H2. unfold fp_dj in H. eapply Forall_impl; [|exact H].
  intros [c d] Hd. cbn beta in Hd. rewrite Forall_forall in Hd. pose proof (Hd _ Hin) as D.
  unfold ly_dj in *. cbn [fst snd] in *. lia.
Qed.

(* A byte list at A after a run that kept every byte of it except the byte at A + j, which now reads b0. *)
Lemma cm_bytes_upd1 : forall W' mm mm2 A bs j b0,
  bytes_at rsegs mm A bs -> munch W' mm mm2 -> 0 <= j < Z.of_nat (length bs) ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> x <> A + j -> outside W' x) ->
  mrd rsegs mm2 (wa (A + j)) = Some b0 ->
  bytes_at rsegs mm2 A (upd_bytes bs (Z.to_nat j) [b0]).
Proof.
  intros W' mm mm2 A bs j b0 (H0 & Hl & HB) Hm Hj HO Hrd.
  assert (L : length (upd_bytes bs (Z.to_nat j) [b0]) = length bs)
    by (apply upd_bytes_length; cbn [length]; lia).
  split; [exact H0|]. split; [rewrite L; exact Hl|].
  intros i Hi. rewrite L in Hi.
  rewrite (upd_bytes_nth bs (Z.to_nat j) [b0] i ltac:(cbn [length]; lia) Hi).
  destruct (Nat.eq_dec i (Z.to_nat j)) as [Ei|Ne].
  - subst i.
    match goal with |- context [if ?c then _ else _] =>
      replace c with true by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt];
                              cbn [length]; lia) end.
    rewrite Nat.sub_diag. cbn [nth_error]. rewrite Z2Nat.id by lia. exact Hrd.
  - assert (KEEP : mrd rsegs mm2 (wa (A + Z.of_nat i)) = nth_error bs i).
    { rewrite <- (HB i Hi). unfold mrd. rewrite Hm; [reflexivity|]. rewrite wa_unsigned by lia. apply HO; lia. }
    rewrite KEEP.
    match goal with |- context [if ?c then _ else _] => destruct c eqn:E; [|reflexivity] end.
    apply andb_true_iff in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. cbn [length] in E2.
    exfalso; lia.
Qed.

Lemma cm_forall_upd : forall (P : byte -> Prop) bs k ws, Forall P bs -> Forall P ws -> Forall P (upd_bytes bs k ws).
Proof.
  intros P bs k ws H Hw. unfold upd_bytes. apply Forall_app. split; [apply cm_forall_firstn; exact H|].
  apply Forall_app. split; [exact Hw | apply cm_forall_skipn; exact H].
Qed.

(* The class-0 and class-1 state lies in [FS, FS + 28672): it survives writes apart from the side stack's first
   36864 bytes except one byte fl at or above FS + 28672. *)
Lemma cm_cls_keep1 : forall W' mm mm2 c fl, (c <= 1)%nat -> FS + 28672 <= fl ->
  (forall x, FS <= x < FS + 36864 -> x <> fl -> outside W' x) -> munch W' mm mm2 ->
  fp_cls mm FS c -> fp_cls mm2 FS c.
Proof.
  intros W' mm mm2 c fl Hc Hfl BEL Hm (Hc6 & h & flags & HH & HFg & HFl & HFb).
  assert (B : FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + 28672 /\
              FS <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + 28672).
  { unfold fs_hint, fs_flag, fs_M. destruct c as [|[|c]]; [simpl; lia | simpl; lia | exfalso; lia]. }
  split; [exact Hc6|]. exists h, flags.
  split; [eapply fl_bytes; [exact HH | exact Hm | intros x Hx; rewrite length_le8 in Hx; apply BEL; lia]|].
  split; [eapply fl_bytes; [exact HFg | exact Hm | intros x Hx; apply BEL; lia]|].
  split; assumption.
Qed.

(* The class-2 state after the release of frame j: the flag byte j reads 0, every other byte of the class-2 state is
   kept. *)
Lemma cm_cls_rel : forall W' mm mm2 j, 0 <= j < fs_M 2 ->
  (forall x, FS <= x < FS + 36864 -> x <> fs_flag FS 2 j -> outside W' x) -> munch W' mm mm2 ->
  mrd rsegs mm2 (wa (fs_flag FS 2 j)) = Some (Z_to_bv 8 0) -> fp_cls mm FS 2 -> fp_cls mm2 FS 2.
Proof.
  intros W' mm mm2 j Hj BEL Hm Hrd (Hc6 & h & flags & HH & HFg & HFl & HFb).
  assert (E1 : fs_hint FS 2 = FS + 16) by (unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; lia).
  assert (E2 : fs_flag FS 2 j = fs_flag FS 2 0 + j) by (unfold fs_flag; lia).
  assert (E3 : fs_flag FS 2 0 = FS + 28672)
    by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 15) with 32768; change (2 ^ 13) with 8192; lia).
  assert (E4 : fs_M 2 = 4096) by reflexivity.
  split; [exact Hc6|]. exists h, (upd_bytes flags (Z.to_nat j) [Z_to_bv 8 0]).
  split; [eapply fl_bytes; [exact HH | exact Hm | intros x Hx; rewrite length_le8 in Hx; apply BEL; lia]|].
  split; [|split].
  - apply (cm_bytes_upd1 W' mm mm2 (fs_flag FS 2 0) flags j (Z_to_bv 8 0) HFg Hm); [lia | | rewrite <- E2; exact Hrd].
    intros x Hx Hne. apply BEL; lia.
  - rewrite upd_bytes_length; [exact HFl | cbn [length]; lia].
  - apply cm_forall_upd; [exact HFb | constructor; [left; reflexivity | constructor]].
Qed.

Ltac tcell DJ sel :=
  eapply fl_bytes; [eassumption | eassumption |
    let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    rewrite ?length_app, ?length_le8, ?length_le4, ?length_le1 in Hx; cbn [length] in Hx;
    eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; sel; reflexivity | lia] ].

Lemma cm_tls_cells : forall mm mm2 W TP DT TS C T DB k,
  asan_tls_cells mm TP DT TS C T DB k -> munch W mm mm2 ->
  fp_dj W (fp_tls TP DT TS C T DB k) ->
  asan_tls_cells mm2 TP DT TS C T DB k.
Proof.
  intros mm mm2 W TP DT TS C T DB k HTl Hm DJ.
  unfold asan_tls_cells in HTl |- *.
  destruct HTl as (c1 & c2 & c3 & c4 & c5 & c6k & c7 & c8 & c9 & c10 & c11ex & c12 & c13 & c14 & c15 & c16 & c17 & c18db & c19).
  split; [tcell DJ ltac:(left)|]. split; [tcell DJ ltac:(do 1 right; left)|].
  split; [tcell DJ ltac:(do 2 right; left)|]. split; [tcell DJ ltac:(do 3 right; left)|].
  split; [tcell DJ ltac:(do 4 right; left)|]. split; [exact c6k|].
  split; [tcell DJ ltac:(do 5 right; left)|]. split; [tcell DJ ltac:(do 6 right; left)|].
  split; [tcell DJ ltac:(do 7 right; left)|]. split; [tcell DJ ltac:(do 8 right; left)|].
  split; [destruct c11ex as (tb & te & c11); exists tb, te; tcell DJ ltac:(do 9 right; left)|].
  split; [tcell DJ ltac:(do 10 right; left)|]. split; [tcell DJ ltac:(do 11 right; left)|].
  split; [tcell DJ ltac:(do 12 right; left)|]. split; [tcell DJ ltac:(do 13 right; left)|].
  split; [tcell DJ ltac:(do 14 right; left)|]. split; [tcell DJ ltac:(do 2 right; left)|].
  split; [exact c18db|]. tcell DJ ltac:(do 15 right; left).
Qed.

(* One store of the shadow byte k of the frame: the memory facts the exit carries are moved across it and the
   24-byte shadow list keeps its value with that byte set to 0 (0xf5 for shstf, a released side-stack frame). *)
Ltac shst fr0 mc0 k :=
  lazymatch goal with
  | [ SHIN : forall kk, _ -> in_shadow (shadow_addr fr0 + kk),
      WMc : wmono rsegs mc0 ?mcur,
      SRcur : shadow_rw ?mcur,
      Jmicur : mem_inv rsegs ?mcur,
      MUc : munch ?W mc0 ?mcur,
      BSH : bytes_at rsegs ?mcur (shadow_addr fr0) ?cs,
      STwcur : stk rsegs ?mcur (S - 9136) S,
      Lcs : length ?cs = 24%nat
      |- evt _ _ (MS _ _ _ _ _ ?mcur _) ] =>
    let SOK := fresh "SOK" in
    assert (SOK : store_ok rsegs mcur (wa (shadow_addr fr0 + k)) 1 = true)
      by (apply cm_sh_sok; [exact SRcur | apply SHIN; lia]);
    step;
    apply (wmono_write rsegs mc0 mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in WMc;
    apply (cm_shadow_rw_write mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in SRcur;
    apply (mem_inv_store rsegs mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in Jmicur;
      [| rewrite length_le1; exact SOK];
    apply (stk_write rsegs mcur (S - 9136) S (shadow_addr fr0 + k) (le1 (Z_to_bv 64 0))) in STwcur;
      [| lia | rewrite length_le1; lia];
    apply (munch_write W mc0 mcur (shadow_addr fr0 + k) (le1 (Z_to_bv 64 0))) in MUc;
      [| lia | rewrite length_le1; lia | rewrite length_le1; cbn [inside]; right; left; split; lia];
    let B2 := fresh "BSHn" in
    pose proof (bytes_at_write_inside rsegs mcur (shadow_addr fr0) cs k (le1 (Z_to_bv 64 0)) BSH ltac:(lia)
                 ltac:(rewrite length_le1, Lcs; lia)) as B2;
    let L2 := fresh "Lcsn" in
    assert (L2 : length (upd_bytes cs (Z.to_nat k) (le1 (Z_to_bv 64 0))) = 24%nat)
      by (rewrite upd_bytes_length; [exact Lcs | rewrite length_le1, Lcs; lia]);
    clear BSH Lcs SOK; rename B2 into BSH; rename L2 into Lcs
  end.

Ltac shstf fr0 mc0 k :=
  lazymatch goal with
  | [ SHIN : forall kk, _ -> in_shadow (shadow_addr fr0 + kk),
      WMc : wmono rsegs mc0 ?mcur,
      SRcur : shadow_rw ?mcur,
      Jmicur : mem_inv rsegs ?mcur,
      MUc : munch ?W mc0 ?mcur,
      STwcur : stk rsegs ?mcur (S - 9136) S
      |- evt _ _ (MS _ _ _ _ _ ?mcur _) ] =>
    let SOK := fresh "SOK" in
    assert (SOK : store_ok rsegs mcur (wa (shadow_addr fr0 + k)) 1 = true)
      by (apply cm_sh_sok; [exact SRcur | apply SHIN; lia]);
    step;
    apply (wmono_write rsegs mc0 mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in WMc;
    apply (cm_shadow_rw_write mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in SRcur;
    apply (mem_inv_store rsegs mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in Jmicur;
      [| rewrite length_le1; exact SOK];
    apply (stk_write rsegs mcur (S - 9136) S (shadow_addr fr0 + k) (le1 (Z_to_bv 64 (-11)))) in STwcur;
      [| lia | rewrite length_le1; lia];
    apply (munch_write W mc0 mcur (shadow_addr fr0 + k) (le1 (Z_to_bv 64 (-11)))) in MUc;
      [| lia | rewrite length_le1; lia | rewrite length_le1; cbn [inside]; right; left; split; lia];
    clear SOK
  end.

(* The exit 0x84724: the frame's first word is set to the frame magic, then on the machine-stack arm the frame's 24
   shadow bytes are set to 0 (the frame is usable again) and on the side-stack arm its 32 shadow bytes to 0xf5
   (released) and the frame's in-use flag byte to 0; a0 = s3 = r, sp and the 12 saved registers are restored from
   [S - 96, S) and the function returns. *)
Lemma cm_exit : forall fr sp2 jj nn mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv fr sp2 jj nn mc ->
  evt rsegs cmPost
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk.
  pose proof (cm_stk_win fr sp2 jj nn mc INVk) as STw.
  pose proof (cm_stk_fr fr sp2 jj nn mc INVk) as STf.
  pose proof INVk as INV.
  destruct INV as (HFK & Jmu & Jwm & Jrm & Jmi & JAC & JSR & JFP & JTL & JAD & JAWX & SAV & FLG).
  pose proof HFK as HFKc.
  pose proof (fk_facts fr sp2 jj nn HFK) as (Fm8 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst nn.
    assert (SOKfr : store_ok rsegs mc (wa fr) 8 = true) by
      (apply (wv_store_ok mc mc fr 8);
        [ intros i Hi; exact (stk_wv mc fr (fr + 192) (fr + i) STf ltac:(lia))
        | apply wmono_refl | lia | lia ]).
    assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (shadow_addr fr + k)).
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply Fap. lia. }
    assert (SBlo : 0 <= shadow_addr fr) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
    assert (SBhi : shadow_addr fr + 32 <= 2 ^ 64) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 23) (SHIN 23 ltac:(lia))); lia).
    assert (OUTW : forall y, S - 9136 <= y < S -> ~ (fr <= y < fr + 192) ->
              outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] (shadow_addr y)).
    { intros y Hy Hyf. pose proof (cmHF_sh_win fr sp2 jj 0 y HFKc Hy Hyf) as Ho.
      unfold cmHF in Ho. cbn [outside] in Ho |- *. destruct Ho as (_ & H2 & H3 & _).
      split; [clear -H2; lia | split; [exact H3 | exact I]]. }
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof JSR as SRcur.
    pose proof Jmi as Jmicur.
    pose proof (munch_refl [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] mc) as MUc.
    pose proof STw as STwcur.
    step. step. step.
    change (Z_to_bv 64 fr) with (wa fr).
    apply (wmono_write rsegs mc mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in WMc.
    apply (cm_shadow_rw_write mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in SRcur.
    apply (mem_inv_store rsegs mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in Jmicur;
      [| rewrite length_le8; exact SOKfr].
    apply (munch_write _ mc mc fr (le8 (Z_to_bv 64 1172321806))) in MUc;
      [| lia | rewrite length_le8; lia | cbn [inside]; left; split; [lia | rewrite length_le8; lia]].
    apply (stk_write rsegs mc (S - 9136) S fr (le8 (Z_to_bv 64 1172321806))) in STwcur;
      [| lia | rewrite length_le8; lia].
    replace (if (0 =? 0)%Z then 0 else fr) with 0 by reflexivity.
    step. rewrite bv_eqb_refl. cbv iota.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (cm_rd_list m1 24 (shadow_addr fr) SBlo ltac:(lia)
        (fun i Hi => proj2 (SRcur (shadow_addr fr + i) (SHIN i ltac:(lia))))) as (cs0 & Lcs & BSH) end.
    assert (LcsO : (24 = length cs0)%nat) by (symmetry; exact Lcs).
    shst fr mc 4. shst fr mc 5. shst fr mc 6. shst fr mc 7. shst fr mc 0. shst fr mc 1. shst fr mc 2. shst fr mc 3.
    shst fr mc 12. shst fr mc 13. shst fr mc 14. shst fr mc 15. shst fr mc 8. shst fr mc 9. shst fr mc 10. shst fr mc 11.
    shst fr mc 20. shst fr mc 21. shst fr mc 22. shst fr mc 23. shst fr mc 16. shst fr mc 17. shst fr mc 18. shst fr mc 19.
    assert (FRup : fr + 320 <= S) by lia.
    assert (SAFup : shadow_addr fr + 24 <= S - 96)
      by (unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (SAVf : rw_cells rsegs mf (S - 96) cmSAVES)
        by (apply (rw_cells_transport rsegs _ mc mf (S - 96) cmSAVES SAV MUc WMc);
            cbn [disjoint_from cells_size csize]; split; [right; lia | split; [right; lia | exact I]]) end.
    clear SAV. unfold cmSAVES in SAVf. replace (S - 96) with (S + -96) in SAVf by lia.
    do 16 step.
    apply evt_done. unfold cmPost. subst r.
    unfold aWc, aXs in Jmu.
    exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6. eexists.
    assert (SUB : sub_fp [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                    ([(S - 9136, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS
                       ++ [(shadow_addr (S - 9136), shadow_addr S)])).
    { intros x Hx. cbn [app outside] in Hx. destruct Hx as (Hx1 & Hx2).
      apply cm_out_app in Hx2. destruct Hx2 as (Hxfp & Hxsh).
      cbn [outside] in Hxsh. destruct Hxsh as (Hxsh & _).
      pose proof (acl_sh_ge fr (S - 9136) ltac:(lia)) as G1.
      pose proof (acl_sh_ge S (fr + 192) ltac:(lia)) as G2.
      replace (fr + 192) with (fr + 8 * 24) in G2 by lia.
      rewrite (cm_sh_add8 fr 24 Fm8) in G2.
      cbn [outside]. split; [| split; [| exact I]].
      - clear -Hx1 Fhi Fpos CAlo CAhi Ef. lia.
      - clear -Hxsh G1 G2. lia. }
    split; [reflexivity|].
    match goal with |- munch _ _ ?Mm /\ _ => set (M := Mm) in * end.
    split; [eapply (munch_trans _ m mc); [exact Jmu | eapply munch_weaken; [exact SUB | exact MUc]] |].
    split; [eapply (wmono_trans rsegs m mc); [exact Jwm | exact WMc] |].
    split; [exact Jmicur |].
    split; [exact STwcur |].
    split; [ eapply fl_asan_cells; [exact JAC | exact MUc |];
             intros x Hx; unfold RT_LO, RT_HI in Hx; cbn [outside];
             split; [ clear -Hx HHM' CAlo CAhi Ef Fhi; lia
                    | split; [ clear -Hx SBlo Fpos; unfold shadow_addr, ASAN_K in *;
                               Z.div_mod_to_equations; lia
                             | exact I ] ] |].
    split; [exact SRcur |].
    split.
    { symmetry in LcsO.
      assert (BSHf : bytes_at rsegs M (shadow_addr fr)
        (fold_left (fun l k => upd_bytes l k (le1 (Z_to_bv 64 0))) cm_ks cs0)) by exact BSH.
      assert (LF : length (fold_left (fun l k => upd_bytes l k (le1 (Z_to_bv 64 0))) cm_ks cs0) = 24%nat)
        by exact Lcs.
      assert (COV : forall q, 0 <= q < 24 -> mrd rsegs M (wa (shadow_addr fr + q)) = Some (Z_to_bv 8 0)).
      { intros q Hq. destruct BSHf as (_ & _ & HBf).
        specialize (HBf (Z.to_nat q) ltac:(rewrite LF; lia)).
        rewrite Z2Nat.id in HBf by lia. rewrite HBf.
        rewrite (cm_nth_fold1 (le1 (Z_to_bv 64 0)) cm_ks (Z.to_nat q) cs0 eq_refl
                   ltac:(rewrite LcsO; lia) ltac:(intros kk Hkk; rewrite LcsO; apply cm_ks_bound; exact Hkk)).
        destruct (in_dec Nat.eq_dec (Z.to_nat q) cm_ks) as [_|Hn]; [reflexivity|].
        exfalso; apply Hn; apply cm_ks_cover; lia. }
      split; [lia | split; [lia | split; [unfold APPMEM_END; lia |]]].
      intros i Hi.
      destruct (Z_lt_le_dec (S - 9136 + i) fr) as [Lo|Lo];
        [| destruct (Z_lt_le_dec (S - 9136 + i) (fr + 192)) as [Inr|Hi2]].
      - exact (cm_ab_keep _ mc M _ (JAWX (S - 9136 + i) ltac:(lia) ltac:(lia)) MUc
                 (OUTW (S - 9136 + i) ltac:(lia) ltac:(lia))).
      - split; [replace (S - 9136 + i) with (fr + (S - 9136 + i - fr)) by lia; apply Fap; lia |].
        exists (Z_to_bv 8 0). split.
        + replace (shadow_addr (S - 9136 + i)) with (shadow_addr fr + (S - 9136 + i - fr) / 8).
          2:{ rewrite <- (cm_sh_div fr (S - 9136 + i - fr) Fm8). f_equal. lia. }
          apply COV. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        + unfold shadow_ok. left. vm_compute. reflexivity.
      - exact (cm_ab_keep _ mc M _ (JAWX (S - 9136 + i) ltac:(lia) ltac:(lia)) MUc
                 (OUTW (S - 9136 + i) ltac:(lia) ltac:(lia))). }
    assert (SG1 : shadow_addr (S - 9136) <= shadow_addr fr) by (apply acl_sh_ge; lia).
    assert (SG2 : shadow_addr fr + 24 <= shadow_addr S).
    { pose proof (acl_sh_ge S (fr + 192) ltac:(lia)) as G.
      replace (fr + 192) with (fr + 8 * 24) in G by lia. rewrite (cm_sh_add8 fr 24 Fm8) in G. exact G. }
    assert (BEL : forall x, FS <= x < FS + FS_SIZE ->
               outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] x).
    { intros x Hx. unfold FS_SIZE in Hx. cbn [outside]. split; [| split; [| exact I]].
      - clear -Hx FShi Fpos Fhi CAlo CAhi Ef. lia.
      - intros [A B]. pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HSx.
        replace (shadow_addr fr + (x - shadow_addr fr)) with x in HSx by lia.
        apply (acl_app_not_shadow x); [apply FSapp; unfold FS_SIZE; lia | exact HSx]. }
    split.
    { destruct JFP as (DT & TS & C & T & DB & kk & HTx & HTP & HP & H88 & H96 & HCL & HFSb & HAb & HWd & HDd).
      pose proof (JTL DT TS C T DB kk HTx) as JTLi.
      assert (DJ : fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                     (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
      { pose proof HWd as HW'. unfold fp_dj in HW'. apply Forall_inv in HW'.
        apply Forall_app in HW' as [HWtls _].
        constructor; [| constructor; [| constructor]].
        - eapply Forall_impl; [| exact HWtls]. intros [a b] Hd. unfold ly_dj in *; cbn [fst snd] in *.
          clear -Hd Fhi Fpos CAlo CAhi Ef. lia.
        - unfold fp_dj in JTLi. eapply Forall_impl; [| exact JTLi]. intros [a b] Hd.
          unfold aXs in Hd. apply Forall_app in Hd as [_ Hd]. apply Forall_inv in Hd.
          unfold ly_dj in *; cbn [fst snd] in *. clear -Hd SG1 SG2. lia. }
      exists DT, TS, C, T, DB, kk.
      split; [eapply cm_tls_cells; [exact HTx | exact MUc | exact DJ]|].
      split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite length_le8 in Hx;
               eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
      split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
               split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4|];
               eapply (stk_transport rsegs _ mc M FS (FS + FS_SIZE));
                 [exact P5 | exact MUc | exact WMc | intros x Hx; left; apply BEL; exact Hx]|].
      split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; rewrite length_le8 in Hx; apply BEL;
               unfold FS_SIZE; lia]|].
      split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; cbn [length] in Hx; apply BEL;
               unfold FS_SIZE; lia]|].
      split; [exact (Forall_impl _ (fun c Hc => fl_cls _ mc M FS c BEL MUc Hc) HCL)|].
      split; [exact HFSb|]. split; [exact HAb|]. split; [exact HWd | exact HDd]. }
    intros DT TS C T DB k HTM.
    destruct JFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
    pose proof (JTL DT0 TS0 C0 T0 DB0 k0 HT0) as JTLi0.
    assert (DJ0 : fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { pose proof HWd as HW'. unfold fp_dj in HW'. apply Forall_inv in HW'.
      apply Forall_app in HW' as [HWtls _].
      constructor; [| constructor; [| constructor]].
      - eapply Forall_impl; [| exact HWtls]. intros [a b] Hd. unfold ly_dj in *; cbn [fst snd] in *.
        clear -Hd Fhi Fpos CAlo CAhi Ef. lia.
      - unfold fp_dj in JTLi0. eapply Forall_impl; [| exact JTLi0]. intros [a b] Hd.
        unfold aXs in Hd. apply Forall_app in Hd as [_ Hd]. apply Forall_inv in Hd.
        unfold ly_dj in *; cbn [fst snd] in *. clear -Hd SG1 SG2. lia. }
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d ->
                   outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] x)
                 (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. eapply fl_dj_out; [exact DJ0 | exact Hin | cbn [fst snd] in Hx; lia]. }
    destruct (fl_tls_same mc M _ (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTM MUc Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact JTLi0.
  - subst nn.
    assert (FRlo : FS + 36864 <= fr).
    { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
    assert (FRhi2 : fr + 256 <= FS + 11571200).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
    assert (SOKfr : store_ok rsegs mc (wa fr) 8 = true) by
      (apply (wv_store_ok mc mc fr 8);
        [ intros i Hi; exact (stk_wv mc fr (fr + 192) (fr + i) STf ltac:(lia))
        | apply wmono_refl | lia | lia ]).
    assert (SHIN : forall k, 0 <= k < 32 -> in_shadow (shadow_addr fr + k)).
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply FSapp.
      unfold FS_SIZE. lia. }
    assert (SBlo : 0 <= shadow_addr fr) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
    assert (SBhi : shadow_addr fr + 40 <= 2 ^ 64) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 31) (SHIN 31 ltac:(lia))); lia).
    assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
    assert (OUTW : forall y, S - 9136 <= y < S ->
              outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                       (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] (shadow_addr y)).
    { intros y Hy.
      assert (Hap : app_mem y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia).
      pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [outside]. split; [| split; [| split; [| exact I]]].
      - apply (sh_out_app (shadow_addr y) fr (fr + 8) Hsh).
        intros z Hz. apply FSapp. unfold FS_SIZE. lia.
      - pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
        rewrite (cm_sh_add8 fr 32 Fm8) in G. lia.
      - apply (sh_out_app (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
        intros z Hz. apply FSapp. unfold FS_SIZE. lia. }
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof JSR as SRcur.
    pose proof Jmi as Jmicur.
    pose proof (munch_refl [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                            (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc) as MUc.
    pose proof STw as STwcur.
    step. step. step.
    change (Z_to_bv 64 fr) with (wa fr).
    apply (wmono_write rsegs mc mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in WMc.
    apply (cm_shadow_rw_write mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in SRcur.
    apply (mem_inv_store rsegs mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in Jmicur;
      [| rewrite length_le8; exact SOKfr].
    apply (munch_write _ mc mc fr (le8 (Z_to_bv 64 1172321806))) in MUc;
      [| lia | rewrite length_le8; lia | cbn [inside]; left; split; [lia | rewrite length_le8; lia]].
    apply (stk_write rsegs mc (S - 9136) S fr (le8 (Z_to_bv 64 1172321806))) in STwcur;
      [| lia | rewrite length_le8; lia].
    replace (if (1 =? 0)%Z then 0 else fr) with fr by reflexivity.
    step. rewrite (cm_eqb0 fr) by lia.
    replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step.
    shstf fr mc 4. shstf fr mc 5. shstf fr mc 6. shstf fr mc 7. shstf fr mc 0. shstf fr mc 1. shstf fr mc 2. shstf fr mc 3.
    shstf fr mc 12. shstf fr mc 13. shstf fr mc 14. shstf fr mc 15. shstf fr mc 8. shstf fr mc 9. shstf fr mc 10. shstf fr mc 11.
    shstf fr mc 20. shstf fr mc 21. shstf fr mc 22. shstf fr mc 23. shstf fr mc 16. shstf fr mc 17. shstf fr mc 18. shstf fr mc 19.
    shstf fr mc 28. shstf fr mc 29. shstf fr mc 30. shstf fr mc 31. shstf fr mc 24. shstf fr mc 25. shstf fr mc 26. shstf fr mc 27.
    specialize (FLG eq_refl).
    pose proof JFP as JFPc.
    destruct JFPc as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & HPfs & _ & _ & _ & _ & _ & _ & _).
    destruct HPfs as (FSP1 & FSP2 & FSP3 & FSP4 & FSPstk).
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (FLGm : bytes_at rsegs m1 (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))))
        by (eapply fl_bytes; [exact FLG | exact MUc |
             intros x Hx; rewrite length_le8 in Hx; cbn [outside];
             split; [lia | split; [ intros [A B];
               apply (acl_app_not_shadow x);
               [ apply FSapp; unfold FS_SIZE; lia
               | pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HS;
                 replace (shadow_addr fr + (x - shadow_addr fr)) with x in HS by lia; exact HS ]
               | split; [ lia | exact I ]]]]);
      assert (RD : ov_read_bytes rsegs m1 (wa (fr + 248)) 8 = Some (le8 (Z_to_bv 64 (fs_flag FS 2 jj))))
        by (replace (fr + 248) with (fr + 248 + 0) by lia;
            rewrite (bytes_at_read rsegs m1 _ (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) 0 8 FLGm)
              by (try rewrite length_le8; lia); reflexivity);
      assert (SOKfl : store_ok rsegs m1 (wa (fs_flag FS 2 jj)) 1 = true)
        by (apply (wv_store_ok mc m1 (fs_flag FS 2 jj) 1);
            [ intros i Hi; replace (fs_flag FS 2 jj + i) with (fs_flag FS 2 jj) by lia;
              exact (stk_wv mc FS (FS + FS_SIZE) (fs_flag FS 2 jj) FSPstk ltac:(unfold FS_SIZE; lia))
            | exact WMc | lia | unfold FS_SIZE in *; lia ]);
      assert (STfs1 : stk rsegs m1 FS (FS + FS_SIZE))
        by (repeat (apply stk_write; [| lia | rewrite ?length_le1, ?length_le8; lia]); exact FSPstk) end.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
    step.
    change (Z_to_bv 64 (fs_flag FS 2 jj)) with (wa (fs_flag FS 2 jj)).
    apply (wmono_write rsegs mc m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in WMc.
    apply (cm_shadow_rw_write m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in SRcur.
    apply (mem_inv_store rsegs m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in Jmicur;
      [| rewrite length_le1; exact SOKfl].
    apply (stk_write rsegs m1 (S - 9136) S (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STwcur;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
    apply (munch_write _ mc m1 (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in MUc;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia
       | rewrite length_le1; cbn [inside]; right; right; left; split; lia].
    apply (stk_write rsegs m1 FS (FS + FS_SIZE) (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STfs1;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
    clearbody m1.
    step.
    assert (SAFup : shadow_addr fr + 40 <= S - 96)
      by (unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (SAVf : rw_cells rsegs mf (S - 96) cmSAVES)
        by (apply (rw_cells_transport rsegs _ mc mf (S - 96) cmSAVES SAV MUc WMc);
            cbn [disjoint_from cells_size csize];
            split; [right; lia | split; [right; lia | split; [right; lia | exact I]]]) end.
    clear SAV. unfold cmSAVES in SAVf. replace (S - 96) with (S + -96) in SAVf by lia.
    do 17 step.
    apply evt_done. unfold cmPost. subst r.
    unfold aWc, aXs in Jmu.
    exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6. eexists.
    assert (FRin : fs_frame FS 2 0 <= fr /\ fr + 256 <= fs_frame FS 2 (fs_M 2)).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj. lia. }
    assert (FLin : fs_flag FS 2 0 <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= fs_flag FS 2 0 + fs_M 2).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 12) with 4096 in Hj. lia. }
    assert (INframe : In (fs_frame FS 2 0, fs_frame FS 2 (fs_M 2)) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (INflag : In (fs_flag FS 2 0, fs_flag FS 2 0 + fs_M 2) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (INsh : In (shadow_addr (fs_frame FS 2 0), shadow_addr (fs_frame FS 2 (fs_M 2)))
                      (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (SG1f : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr) by (apply acl_sh_ge; destruct FRin; lia).
    assert (SG2f : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
    { pose proof (cm_sh_add8 fr 32 Fm8) as E. replace (fr + 8 * 32) with (fr + 256) in E by lia. rewrite <- E.
      apply acl_sh_ge. destruct FRin; lia. }
    assert (SUB : sub_fp [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                          (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                    ([(S - 9136, S)] ++ fp_w [0%nat;1%nat;2%nat] FS
                       ++ [(shadow_addr (S - 9136), shadow_addr S)])).
    { intros x Hx. cbn [app outside] in Hx. destruct Hx as (_ & Hx2).
      apply cm_out_app in Hx2. destruct Hx2 as (Hxfp & _). cbn [outside].
      split; [| split; [| split; [| exact I]]].
      - intros Hcc. apply (out_in _ _ _ x Hxfp INframe). destruct FRin as (A1 & A2). lia.
      - intros Hcc. apply (out_in _ _ _ x Hxfp INsh). lia.
      - intros Hcc. apply (out_in _ _ _ x Hxfp INflag). destruct FLin as (B1 & B2). lia. }
    split; [reflexivity|].
    match goal with |- munch _ _ ?Mm /\ _ => set (M := Mm) in * end.
    split; [eapply (munch_trans _ m mc); [exact Jmu | eapply munch_weaken; [exact SUB | exact MUc]] |].
    split; [eapply (wmono_trans rsegs m mc); [exact Jwm | exact WMc] |].
    split; [exact Jmicur |].
    split; [exact STwcur |].
    split; [ eapply fl_asan_cells; [exact JAC | exact MUc |];
             intros x Hx; unfold RT_LO, RT_HI, ASAN_GT in *; cbn [outside];
             split; [ clear -Hx FSgt FRlo; unfold ASAN_GT in *; lia
                    | split; [ clear -Hx SBlo Fpos; unfold shadow_addr, ASAN_K in *;
                               Z.div_mod_to_equations; lia
                             | split; [ clear -Hx FSgt FLo; unfold ASAN_GT in *; lia | exact I ] ] ] |].
    split; [exact SRcur |].
    assert (M2 : fs_M 2 = 4096) by reflexivity.
    assert (FLv : fs_flag FS 2 jj = FS + 28672 + jj)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 15) with 32768;
          change (2 ^ 13) with 8192; lia).
    pose proof FRin as (FRa & FRb). pose proof FLin as (FLa & FLb).
    assert (BELh : forall x, FS <= x < FS + 36864 -> x <> fs_flag FS 2 jj ->
              outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                       (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x).
    { intros x Hx Hne. cbn [outside]. split; [lia | split; [| split; [lia | exact I]]].
      intros [A B]. apply (acl_app_not_shadow x); [apply FSapp; unfold FS_SIZE; lia |].
      pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HS.
      replace (shadow_addr fr + (x - shadow_addr fr)) with x in HS by lia. exact HS. }
    assert (RDfl : mrd rsegs M (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0)).
    { change (mrd rsegs (write_to_mem m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) (wa (fs_flag FS 2 jj))
              = Some (Z_to_bv 8 0)).
      pose proof (bytes_at_write_same rsegs m1 (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0)) ltac:(lia)
                    ltac:(rewrite length_le1; unfold FS_SIZE in *; lia)) as BW.
      destruct BW as (_ & _ & BW). specialize (BW 0%nat ltac:(rewrite length_le1; lia)).
      replace (fs_flag FS 2 jj + Z.of_nat 0) with (fs_flag FS 2 jj) in BW by lia.
      rewrite BW. reflexivity. }
    assert (DJall : forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
              fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                     (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                    (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
    { intros DT TS C T DB kk HTx. pose proof (JTL DT TS C T DB kk HTx) as JTLi. unfold aXs in JTLi.
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - apply (cm_dj_in _ _ (fs_frame FS 2 0) (fs_frame FS 2 (fs_M 2)) fr (fr + 8) JTLi);
          [apply in_or_app; left; exact INframe | destruct FRin; lia | destruct FRin; lia].
      - apply (cm_dj_in _ _ (shadow_addr (fs_frame FS 2 0)) (shadow_addr (fs_frame FS 2 (fs_M 2)))
                 (shadow_addr fr) (shadow_addr fr + 32) JTLi); [apply in_or_app; left; exact INsh | lia | lia].
      - apply (cm_dj_in _ _ (fs_flag FS 2 0) (fs_flag FS 2 0 + fs_M 2) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1)
                 JTLi); [apply in_or_app; left; exact INflag | destruct FLin; lia | destruct FLin; lia]. }
    split.
    { split; [lia | split; [lia | split; [unfold APPMEM_END; lia |]]].
      intros i Hi.
      exact (cm_ab_keep _ mc M _ (JAWX (S - 9136 + i) ltac:(lia) ltac:(lia)) MUc
               (OUTW (S - 9136 + i) ltac:(lia))). }
    split.
    { destruct JFP as (DT & TS & C & T & DB & kk & HTx & HTP & HP & H88 & H96 & HCL & HFSb & HAb & HWd & HDd).
      pose proof (DJall DT TS C T DB kk HTx) as DJ.
      exists DT, TS, C, T, DB, kk.
      split; [eapply cm_tls_cells; [exact HTx | exact MUc | exact DJ]|].
      split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite length_le8 in Hx;
               eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
      split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
               split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4 | exact STfs1]|].
      split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; rewrite length_le8 in Hx; apply BELh; lia]|].
      split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; cbn [length] in Hx; apply BELh; lia]|].
      split.
      { apply Forall_cons_iff in HCL as [HC0 HCL]. apply Forall_cons_iff in HCL as [HC1 HCL].
        apply Forall_cons_iff in HCL as [HC2 _].
        constructor; [exact (cm_cls_keep1 _ mc M 0%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC0)|].
        constructor; [exact (cm_cls_keep1 _ mc M 1%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC1)|].
        constructor; [exact (cm_cls_rel _ mc M jj Hj BELh MUc RDfl HC2) | constructor]. }
      split; [exact HFSb|]. split; [exact HAb|]. split; [exact HWd | exact HDd]. }
    intros DT TS C T DB k HTM.
    destruct JFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _).
    pose proof (JTL DT0 TS0 C0 T0 DB0 k0 HT0) as JTLi0.
    pose proof (DJall DT0 TS0 C0 T0 DB0 k0 HT0) as DJ0.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d ->
                   outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                            (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x)
                 (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. eapply fl_dj_out; [exact DJ0 | exact Hin | cbn [fst snd] in Hx; lia]. }
    destruct (fl_tls_same mc M _ (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTM MUc Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact JTLi0.
Qed.

(* The no-match join 0x84704: the five shadow bytes 4 .. 8 of the frame (the parse buffer) are set to 0xf8 (the
   variable is out of scope), then the exit at 0x84724 with s3 = r = want CM_T len fb. *)
Lemma cm_tail : forall fr sp2 jj nn mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv fr sp2 jj nn mc ->
  evt rsegs cmPost
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84704) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk.
  pose proof INVk as INV.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
    unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold cmHF in MUh.
  step.
  cm_wst (shadow_addr fr + 4) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 5) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 6) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 7) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 8) 1%nat. step. store_done.
  step.
  eapply (cm_exit fr sp2 jj nn _ r); [exact Er|].
  eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* The no-row tail 0x84700: the result register s3 is set to 0 and the run joins the tail (cm_tail) with
   r = 0 = want CM_T len fb. *)
Lemma cm_none_holds : cmNone cmPost.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6
    Hw INVk.
  step.
  exact (cm_tail fr sp2 jj nn mc 0 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10
           rt3 rt4 rt5 rt6 ltac:(symmetry; exact Hw) INVk).
Qed.

(* The row-match tail 0x84864: the model buffer's four shadow bytes 14 .. 17 are set to 0xf8 again and the run
   joins the tail (cm_tail) with r = the matching row's address. *)
Lemma cm_hit_holds : cmHit cmPost.
Proof.
  intros fr sp2 jj nn r mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6
    Hw INVk.
  pose proof INVk as INV.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
    unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold cmHF in MUh.
  step.
  cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
  step.
  eapply (cm_tail fr sp2 jj nn _ r); [symmetry; exact Hw|].
  eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* The catalogue-miss tail 0x84720: the result register s3 is set to 0 and the run reaches the exit (cm_exit). *)
Lemma cm_miss_holds : cmMiss cmPost.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hw INVk.
  step.
  exact (cm_exit fr sp2 jj nn mc 0 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 (Z_to_bv 64 len) (wa ASAN_K)
           s8 s9 s10 rt3 rt4 rt5 rt6 ltac:(symmetry; exact Hw) INVk).
Qed.

(* The gate and everything after it: the gate's tests reach the parse call (cm_gate) or the miss tail
   (cm_miss_holds); the call and the row loop (cm_calls) end in the no-row tail (cm_none_holds) or the row-match
   tail (cm_hit_holds). *)
Lemma cm_body : cmKB cmPost.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 INVk.
  apply (cm_gate cmPost fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6);
    [ apply cm_calls; [exact cm_none_holds | exact cm_hit_holds]
    | exact cm_miss_holds
    | exact INVk ].
Qed.

End Match.

(* The contract of reac_box_catalogue_match_c.v from the contracts of the four callees: the entry run takes the
   class-2 frame (or the machine-stack arm), writes the frame words and their shadow bytes and reaches the gate
   (cm_entry) in the state cmKB names; from there the gate's tests, the reac_ctrl_parse call, the 11-row loop with
   the reac_box_model_block call and the bcmp wrapper, and the tails and the exit (cm_body) reach the state cmPost,
   which is the contract's post. *)
Theorem reac_box_catalogue_match_holds :
  reac_ctrl_parse_contract -> reac_box_model_block_contract -> bcmp_wrap_contract ->
  asan_stack_malloc_2_contract -> reac_box_catalogue_match_contract.
Proof.
  intros HPC HMB HBC HSM.
  unfold reac_box_catalogue_match_contract, REAC_BOX_CATALOGUE_MATCH, CM_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HF HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0.
  subst a0 a1 sp.
  eapply cm_entry; try eassumption.
  apply cm_body; assumption.
Qed.
