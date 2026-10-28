(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure MallocShape.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixCopyTR O23LeptRbLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr V23LeptCount.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptRb2W.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptRot90cwW V23LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require SeqExec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition CNT_STACK : Z := 112 + CALLOC_STACK + LSF.
(* [comment removed for export] *)
Definition CNTM0 (m : word -> option byte) (pc : Z) : word -> option byte := wbytes m (Z_to_bv 64 pc) (word_to_le_bytes 4 (Z_to_bv 64 0)).
Definition CNTM (m : word -> option byte) (pc : Z) (wv : word) : word -> option byte := wbytes (CNTM0 m pc) (Z_to_bv 64 pc) (word_to_le_bytes 4 wv).

Lemma str_cnt_msg : str16 0x1189d 29.
Proof. str16_tac. Qed.
Lemma str_cnt : str16 0x1629e 14.
Proof. str16_tac. Qed.

Definition CPC (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19); (s - 48, getr regs 20);
   (s - 56, getr regs 21); (s - 64, getr regs 22); (s - 72, getr regs 23); (s - 80, getr regs 24); (s - 88, getr regs 25); (s - 96, getr regs 26)]%Z.
Definition FTc (tab : Z) (mB m : word -> option byte) : Prop := forall a : word, ~ (tab <= bv_unsigned a < tab + 1024)%Z -> m a = mB a.
Definition TABP (m : word -> option byte) (tab k : Z) : Prop :=
  forall j : Z, (0 <= j < k)%Z -> exists t : Z, (0 <= t <= 8)%Z /\ rdn SEGS m (Z_to_bv 64 (tab + 4 * j)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 t)).

Ltac rzm HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac rzp MP RUN := eapply rz_msteps; [exact (mp_halted _ MP) | exact (mp_lazy _ MP) | exact RUN |].
Ltac fa12 := repeat (apply Forall_cons; [cbn [fst]; lia |]); apply Forall_nil.

Lemma cnt_wb_congr : forall bs (m1 m2 : word -> option byte) (a x : word), m1 x = m2 x -> wbytes m1 a bs x = wbytes m2 a bs x.
Proof.
  induction bs as [|b bs IH]; intros m1 m2 a x E; cbn [wbytes]; [exact E|].
  apply IH. cbv beta. destruct (bv_eqb x a); [reflexivity | exact E].
Qed.

Lemma cnt_m4 : forall a j, (a mod 4 = 0)%Z -> ((a + 4 * j) mod 4 = 0)%Z.
Proof. intros a j H. rewrite (Z.mul_comm 4 j), Z.mod_add by lia. exact H. Qed.

Lemma cnt_line : forall data wpl h i, (0 <= i < h)%Z -> (1 <= wpl)%Z ->
  (data <= data + 4 * wpl * i)%Z /\ (data + 4 * wpl * i + 4 * wpl <= data + 4 * wpl * h)%Z.
Proof. intros data wpl h i Hi Hw. split; nia. Qed.

Lemma cnt_wdiv : forall w, (1 <= w <= 20000)%Z ->
  (0 <= w / 32 <= wpl_of w 1)%Z /\ (0 <= w mod 32 < 32)%Z /\ (1 <= w mod 32 -> w / 32 + 1 <= wpl_of w 1)%Z /\
  (w / 32 = 0 -> 1 <= w mod 32)%Z /\ (w / 32 <= 625)%Z.
Proof.
  intros w Hw. unfold wpl_of. rewrite Z.mul_1_r.
  pose proof (Z.div_mod w 32 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound w 32 ltac:(lia)) as M1.
  pose proof (Z.div_mod (w + 31) 32 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (w + 31) 32 ltac:(lia)) as M2.
  lia.
Qed.

Lemma cnt_tabp_step : forall m (tab k tv : Z), (0 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z -> (0 <= k < 256)%Z -> (0 <= tv <= 8)%Z ->
  TABP m tab k -> TABP (wbytes m (Z_to_bv 64 (tab + 4 * k)) (word_to_le_bytes 4 (Z_to_bv 64 tv))) tab (k + 1).
Proof.
  intros m tab k tv Ht Ht2 Hk Htv TP j Hj.
  destruct (Z.eq_dec j k) as [->|NE].
  - exists tv. split; [exact Htv|].
    pose proof (SeqExec.rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 tv)) m (Z_to_bv 64 (tab + 4 * k))) as R.
    rewrite length_N_to_le_bytes in R. apply R. rewrite u_Z2bv by lia. change (Z.of_nat 4) with 4%Z. lia.
  - destruct (TP j ltac:(lia)) as (t & Ht8 & R). exists t. split; [exact Ht8|].
    rewrite rdn_wbytes_out_Z; [exact R|]. rewrite length_N_to_le_bytes. change (Z.of_nat 4) with 4%Z. lia.
Qed.

Lemma cnt_tab8_frame : forall m m' (tab : Z), (0 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z -> TAB8 m tab ->
  (forall x : word, (tab <= bv_unsigned x < tab + 1024)%Z -> m' x = m x) -> TAB8 m' tab.
Proof.
  intros m m' tab Ht Ht2 TB E k Hk. destruct (TB k Hk) as (t & Ht8 & R). exists t. split; [exact Ht8|].
  rewrite <- R. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply E. cbn in Hx. lia.
Qed.

Section CountW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma cnt_postm_cell : forall C A s m1 mk (a : word) bs, POSTM C A s m1 mk -> POSTM C A s (wbytes m1 a bs) (wbytes mk a bs).
Proof.
  intros C A s m1 mk a bs [F L]. split.
  - intros x H1 H2 H3 H4 H5. apply cnt_wb_congr. exact (F x H1 H2 H3 H4 H5).
  - intros q k i Hq Hi. apply cnt_wb_congr. exact (L q k i Hq Hi).
Qed.

Lemma cnt_entry : forall C A m md regs (s pc : Z) (ret : word), Cok C -> W C A m md ->
  (c_top C - LSTK + 112 <= s)%Z -> (s <= pc)%Z -> (pc + 4 <= c_top C)%Z -> (128 <= s)%Z -> (pc + 4 < 2 ^ 64)%Z ->
  W C A (MCP_A m s pc ret regs) md /\ POSTM C A s (CNTM0 m pc) (MCP_A m s pc ret regs) /\ cellsZ (MCP_A m s pc ret regs) (CPC s ret regs).
Proof.
  intros C A m md regs s pc ret CK HW Hlo Hpc Hpc2 Hs Hpc64.
  assert (WPF : W C A (FCP m s ret regs) md /\ POSTM C A s m (FCP m s ret regs)) by (unfold FCP; wp_win CK).
  destruct WPF as [HWF PMF]. split; [|split].
  - unfold MCP_A. apply (W_store_win C A _ md); [exact CK | exact HWF | rewrite u_Z2bv by lia; lia
                                                | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - exact (cnt_postm_cell C A s m _ (Z_to_bv 64 pc) _ PMF).
  - unfold MCP_A, FCP, CPC. cbn [cellsZ]. repeat split; rdn_solve.
Qed.

(* [comment removed for export] *)
Theorem pixCountPixels_null_W : forall C A m md regs (s pc : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CNT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pc -> (s <= pc)%Z -> (pc + 4 <= c_top C)%Z ->
  (pc mod 4 = 0)%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s (CNTM0 m pc) m' -> getr regs' 10 = Z_to_bv 64 1 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x7e6fc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pc ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 Hpc Hpc2 ALpc HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof (u64_range (c_sp0 C)) as Usp.
  unfold CNT_STACK, CALLOC_STACK, ALLOC_STACK, LSF in Hlo.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (W_sok_win C A m md pc 4 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKc.
  destruct (cnt_entry C A m md regs s pc ret CK HW ltac:(lia) Hpc Hpc2 ltac:(lia) ltac:(lia)) as (HW1 & PM1 & _).
  destruct (cp_An al_rom regs m s pc ret ltac:(lia) ltac:(lia) Hpc ltac:(lia) ALpc SOK SOKc
              (W_sev_got C A _ md HW1) (W_sev C A _ md HW1) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & AG1).
  rzm HW RUN1.
  apply (returnErrorInt_W C A (MCP_A m s pc ret regs) md r1 s 0x1189d 0x1629e 29 14 ret (Z_to_bv 64 1) S CK HW1 Q2 Hs16
           ltac:(unfold LSF; lia) Hhi Q1 Hret Q10 Q11 Q12 str_cnt_msg str_cnt).
  intros m2 r2 HW2 OUT2 MG2 CS2 V10.
  apply (HK m2 r2 HW2).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A _ md m2); [exact CK | exact HW1 | exact OUT2 | unfold LSF; lia | lia | lia].
  - exact V10.
Qed.

(* [comment removed for export] *)
Lemma cp_tab_W : forall C A A1 md mB (s tab : Z) (S : TSet),
  Cok C -> sub_live A A1 -> live A1 (Z_to_bv 64 tab) = Some 1024%Z -> live A (Z_to_bv 64 tab) = None ->
  live (c_A0 C) (Z_to_bv 64 tab) = None -> (4096 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z -> (tab mod 4 = 0)%Z ->
  forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (k : Z),
  W C A1 m md -> POSTM C A s mB m -> FTc tab mB m -> TABP m tab k -> (0 <= k)%Z -> (Z.of_nat n = 255 - k)%Z ->
  regs_agree (fun x => In x [5; 6; 7; 10; 13; 14; 15; 16; 17; 19; 28; 29]%list) r0 r ->
  getr r 18 = Z_to_bv 64 tab -> getr r 11 = Z_to_bv 64 1 -> getr r 12 = Z_to_bv 64 1 -> getr r 10 = Z_to_bv 64 k ->
  getr r 13 = Z_to_bv 64 (tab + 4 * k) -> getr r 14 = Z_to_bv 64 (tab + 4 * k) -> getr r 19 = Z_to_bv 64 (256 - k) ->
  (forall m' r', W C A1 m' md -> POSTM C A s mB m' -> FTc tab mB m' -> TAB8 m' tab ->
     regs_agree (fun x => In x [5; 6; 7; 10; 13; 14; 15; 16; 17; 19; 28; 29]%list) r0 r' ->
     realizes SEGS (mkCfg (mkst r' (0x7e818 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x7e798 : word) m al_rom) md) S.
Proof.
  intros C A A1 md mB s tab S CK SUB Lt Ltr Lt0 Ht Ht2 ALt.
  induction n as [|n IH]; intros r0 r m k HW PM FT TP Hk Hn AG R18 R11 R12 R10 R13 R14 R19 HC.
  all: pose proof (V23LeptRot90cwW.r90w_sok_blk C A1 m md (Z_to_bv 64 tab) 1024 (tab + 4 * k) 4 CK HW Lt
                     ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia)) as SOK.
  all: destruct (cp_T al_rom r m tab k ltac:(lia) Ht Ht2 ALt SOK R18 R11 R12 R10 R13 R14 R19)
         as (r1 & tv & Htv & RUN & V10 & V13 & V14 & V19 & AG1).
  all: rzm HW RUN.
  all: assert (HW1 : W C A1 (wbytes m (Z_to_bv 64 (tab + 4 * k)) (word_to_le_bytes 4 (Z_to_bv 64 tv))) md)
         by (eapply W_store_blk; [exact CK | exact HW | exact Lt | exact Lt0 | rewrite !u_Z2bv by lia; lia
                                 | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
  all: assert (PM1 : POSTM C A s mB (wbytes m (Z_to_bv 64 (tab + 4 * k)) (word_to_le_bytes 4 (Z_to_bv 64 tv))))
         by (eapply POSTM_trans; [exact PM|]; eapply (POSTM_blk C A A1 m md (Z_to_bv 64 tab));
             [exact CK | exact HW | exact Lt | exact Ltr | exact SUB | rewrite !u_Z2bv by lia; lia
             | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
  all: assert (FT1 : FTc tab mB (wbytes m (Z_to_bv 64 (tab + 4 * k)) (word_to_le_bytes 4 (Z_to_bv 64 tv))))
         by (intros a Ha; rewrite wbytes_outside; [apply FT; exact Ha | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                                                  | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  all: pose proof (cnt_tabp_step m tab k tv ltac:(lia) Ht2 ltac:(lia) Htv TP) as TP1.
  - assert (Ek : k = 255%Z) by lia. subst k.
    pose proof (cp_Tx al_rom r1 (wbytes m (Z_to_bv 64 (tab + 4 * 255)) (word_to_le_bytes 4 (Z_to_bv 64 tv)))
                  ltac:(rewrite V19; reflexivity)) as RUN2.
    rzm HW1 RUN2.
    apply HC; [exact HW1 | exact PM1 | exact FT1 | exact TP1 | eapply regs_agree_trans; [exact AG | exact AG1]].
  - pose proof (cp_Tn al_rom r1 (wbytes m (Z_to_bv 64 (tab + 4 * k)) (word_to_le_bytes 4 (Z_to_bv 64 tv)))
                  (256 - (k + 1)) ltac:(lia) V19) as RUN2.
    rzm HW1 RUN2.
    apply (IH r0 r1 _ (k + 1)%Z HW1 PM1 FT1 TP1 ltac:(lia) ltac:(lia) ltac:(eapply regs_agree_trans; [exact AG | exact AG1])
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) V10 V13 V14 V19 HC).
Qed.

Record CROW (m : word -> option byte) (md : Model) (data wpl h tab fw eb : Z) : Prop := MKCROW {
  cr_md : md_pure md;
  cr_tab8 : TAB8 m tab;
  cr_rd : forall a : Z, (data <= a)%Z -> (a + 4 <= data + 4 * wpl * h)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) 4 = Some bs;
  cr_data : (4096 <= data)%Z;
  cr_dal : (data mod 4 = 0)%Z;
  cr_top : (data + 4 * wpl * h < 2 ^ 64)%Z;
  cr_tab : (4096 <= tab)%Z;
  cr_tab2 : (tab + 1024 < 2 ^ 64)%Z;
  cr_tal : (tab mod 4 = 0)%Z;
  cr_h : (1 <= h < 2 ^ 31)%Z;
  cr_wpl : (1 <= wpl < 2 ^ 24)%Z;
  cr_fw : (0 <= fw <= wpl)%Z;
  cr_eb : (0 <= eb < 32)%Z;
  cr_fe : (1 <= eb -> fw + 1 <= wpl)%Z;
  cr_f0 : (fw = 0 -> 1 <= eb)%Z;
  cr_cnt : (h * (32 * fw + 32) < 2 ^ 31)%Z
}.

(* [comment removed for export] *)
Lemma cp_facts : forall C A m md (p : word) (n : Z), Cok C -> W C A m md -> live A p = Some n -> (0 < n)%Z ->
  (4096 <= u p)%Z /\ (u p + n <= alloc_top (c_vm C))%Z /\ (u p mod 16 = 0)%Z.
Proof.
  intros C A m md p n CK HW L Hn.
  destruct (blk_range C A m md p n CK HW L Hn) as [G T].
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (_ & AL16 & _).
  exact (conj G (conj T AL16)).
Qed.

Lemma cp_words_W : forall m md (data wpl h tab fw eb : Z) (S : TSet), CROW m md data wpl h tab fw eb ->
  forall (n : nat) (r0 r : bvmap 5 word) (line j c : Z),
  (data <= line)%Z -> (line + 4 * wpl <= data + 4 * wpl * h)%Z -> (line mod 4 = 0)%Z ->
  (0 <= j)%Z -> (Z.of_nat n = fw - 1 - j)%Z -> (0 <= c)%Z -> (c + 32 * (fw - j) < 2 ^ 31)%Z ->
  regs_agree (fun x => In x [12; 20; 21; 22; 23; 24; 25; 26]%list) r0 r ->
  getr r 10 = Z_to_bv 64 line -> getr r 22 = Z_to_bv 64 (line + 4 * j) -> getr r 21 = Z_to_bv 64 (line + 4 * j) ->
  getr r 20 = Z_to_bv 64 (fw - j) -> getr r 18 = Z_to_bv 64 tab -> getr r 14 = Z_to_bv 64 (2 ^ 64 - 1 - tab) ->
  getr r 12 = Z_to_bv 64 c -> getr r 30 = Z_to_bv 64 1 -> getr r 31 = Z_to_bv 64 1 ->
  (forall (r' : bvmap 5 word) (c' : Z), regs_agree (fun x => In x [12; 20; 21; 22; 23; 24; 25; 26]%list) r0 r' ->
     getr r' 12 = Z_to_bv 64 c' -> (c <= c' <= c + 32 * (fw - j))%Z ->
     realizes SEGS (mkCfg (mkst r' (0x7e980 : word) m al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x7e8b0 : word) m al_rom) md) S.
Proof.
  intros m md data wpl h tab fw eb S CR. pose proof CR as [MP TB RD Hd Hdal Htop Ht Ht2 Htal Hh Hwpl Hfw Heb Hfe Hf0 Hcnt].
  induction n as [|n IH]; intros r0 r line j c Hl Hl2 Hlal Hj Hn Hc Hc2 AG R10 R22 R21 R20 R18 R14 R12 R30 R31 HC.
  all: destruct (RD (line + 4 * j)%Z ltac:(lia) ltac:(lia)) as [bs RB].
  all: destruct (cp_Wd al_rom r m line (line + 4 * j) tab c bs ltac:(lia) ltac:(lia) (cnt_m4 line j Hlal) Ht Ht2 Htal Hc ltac:(lia)
                  RB TB R10 R22 R21 R18 R14 R12 R30 R31) as (r1 & d & Hd32 & RUN1 & V12 & AG1).
  all: rzp MP RUN1.
  - destruct (cp_Wx al_rom r1 m (line + 4 * j) ltac:(lia) ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
                ltac:(csr; f_equal; lia)) as (r2 & RUN2 & AG2).
    rzp MP RUN2.
    apply (HC r2 (c + d)%Z).
    + eapply regs_agree_trans; [eapply regs_agree_trans; [exact AG | regs_agree_weaken AG1] | regs_agree_weaken AG2].
    + csr; reflexivity.
    + lia.
  - destruct (cp_Wn al_rom r1 m (line + 4 * j) (fw - j) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
                ltac:(csr; reflexivity)) as (r2 & RUN2 & V22 & V21 & V20 & AG2).
    rzp MP RUN2.
    apply (IH r0 r2 line (j + 1)%Z (c + d)%Z Hl Hl2 Hlal ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + eapply regs_agree_trans; [eapply regs_agree_trans; [exact AG | regs_agree_weaken AG1] | regs_agree_weaken AG2].
    + csr; reflexivity.
    + rewrite V22; f_equal; lia.
    + rewrite V21; f_equal; lia.
    + rewrite V20; f_equal; lia.
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + intros r' c' AG' E' B'. apply (HC r' c' AG' E'). lia.
Qed.

(* [comment removed for export] *)
Lemma cp_eb_W : forall m md (data wpl h tab fw eb : Z) (S : TSet), CROW m md data wpl h tab fw eb ->
  forall (r : bvmap 5 word) (line c : Z),
  (1 <= eb)%Z -> (data <= line)%Z -> (line + 4 * wpl <= data + 4 * wpl * h)%Z -> (line mod 4 = 0)%Z ->
  (0 <= c)%Z -> (c + 32 < 2 ^ 31)%Z ->
  getr r 10 = Z_to_bv 64 line -> getr r 31 = Z_to_bv 64 fw -> getr r 18 = Z_to_bv 64 tab -> getr r 14 = Z_to_bv 64 (2 ^ 64 - 1 - tab) ->
  getr r 12 = Z_to_bv 64 c -> getr r 16 = Z_to_bv 64 0 -> getr r 30 = Z_to_bv 64 1 ->
  (forall (r' : bvmap 5 word) (c' : Z), regs_agree (fun x => In x [12; 20; 21; 22; 31]%list) r r' ->
     getr r' 12 = Z_to_bv 64 c' -> (c <= c' <= c + 32)%Z ->
     realizes SEGS (mkCfg (mkst r' (0x7ea70 : word) m al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x7e994 : word) m al_rom) md) S.
Proof.
  intros m md data wpl h tab fw eb S CR. pose proof CR as [MP TB RD Hd Hdal Htop Ht Ht2 Htal Hh Hwpl Hfw Heb Hfe Hf0 Hcnt].
  intros r line c Heb1 Hl Hl2 Hlal Hc Hc2 R10 R31 R18 R14 R12 R16 R30 HC.
  destruct (RD (line + 4 * fw)%Z ltac:(lia) ltac:(lia)) as [bs RB].
  destruct (cp_Eb al_rom r m line fw tab c bs ltac:(lia) ltac:(lia) ltac:(lia) Hlal Ht Ht2 Htal Hc Hc2 RB TB R10 R31 R18 R14 R12 R16 R30)
    as (r1 & d & Hd32 & RUN1 & V12 & AG1).
  rzp MP RUN1.
  apply (HC r1 (c + d)%Z AG1 V12). lia.
Qed.

(* [comment removed for export] *)
Lemma cp_row_W : forall m md (data wpl h tab fw eb : Z) (S : TSet), CROW m md data wpl h tab fw eb ->
  forall (r : bvmap 5 word) (line c : Z),
  (data <= line)%Z -> (line + 4 * wpl <= data + 4 * wpl * h)%Z -> (line mod 4 = 0)%Z ->
  (0 <= c)%Z -> (c + 32 * fw + 32 < 2 ^ 31)%Z ->
  getr r 10 = Z_to_bv 64 line -> getr r 29 = Z_to_bv 64 line -> getr r 28 = Z_to_bv 64 1 ->
  getr r 5 = Z_to_bv 64 fw -> getr r 7 = Z_to_bv 64 fw -> getr r 17 = Z_to_bv 64 eb ->
  getr r 18 = Z_to_bv 64 tab -> getr r 14 = Z_to_bv 64 (2 ^ 64 - 1 - tab) -> getr r 16 = Z_to_bv 64 0 -> getr r 12 = Z_to_bv 64 c ->
  (forall (r' : bvmap 5 word) (c' : Z), regs_agree (fun x => In x [12; 20; 21; 22; 23; 24; 25; 26; 30; 31]%list) r r' ->
     getr r' 12 = Z_to_bv 64 c' -> getr r' 30 = Z_to_bv 64 1 -> (c <= c' <= c + 32 * fw + 32)%Z ->
     realizes SEGS (mkCfg (mkst r' (0x7ea70 : word) m al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x7e884 : word) m al_rom) md) S.
Proof.
  intros m md data wpl h tab fw eb S CR. pose proof CR as [MP TB RD Hd Hdal Htop Ht Ht2 Htal Hh Hwpl Hfw Heb Hfe Hf0 Hcnt].
  intros r line c Hl Hl2 Hlal Hc Hc2 R10 R29 R28 R5 R7 R17 R18 R14 R16 R12 HC.
  destruct (Z.eq_dec fw 0) as [F0|F1].
  - subst fw.
    destruct (cp_R0 al_rom r m eb line ltac:(lia) ltac:(lia) R5 R17 R10) as (r1 & RUN1 & V30 & V31 & AG1).
    rzp MP RUN1.
    apply (cp_eb_W m md data wpl h tab 0 eb S CR r1 line c ltac:(lia) Hl Hl2 Hlal Hc ltac:(lia)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)).
    intros r2 c2 AG2 E2 B2. apply (HC r2 c2).
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    + exact E2.
    + csr; reflexivity.
    + lia.
  - destruct (cp_Rw al_rom r m fw line ltac:(lia) ltac:(lia) R5 R7 R10 R29 R28) as (r1 & RUN1 & V30 & V31 & V20 & V21 & V22 & AG1).
    rzp MP RUN1.
    apply (cp_words_W m md data wpl h tab fw eb S CR (Z.to_nat (fw - 1)) r1 r1 line 0 c Hl Hl2 Hlal ltac:(lia) ltac:(lia) Hc ltac:(lia)
             (regs_agree_refl _ _) ltac:(csr; reflexivity) ltac:(csr; f_equal; lia) ltac:(csr; f_equal; lia) ltac:(csr; f_equal; lia)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)).
    intros r2 c2 AG2 E2 B2.
    destruct (Z.eq_dec eb 0) as [E0|E1].
    + subst eb.
      destruct (cp_Xn al_rom r2 m ltac:(csr; reflexivity)) as (r3 & RUN3 & AG3).
      rzp MP RUN3.
      apply (HC r3 c2).
      * eapply regs_agree_trans; [eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2] | regs_agree_weaken AG3].
      * csr; reflexivity.
      * csr; reflexivity.
      * lia.
    + destruct (cp_Xe al_rom r2 m fw eb ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r3 & RUN3 & V31' & AG3).
      rzp MP RUN3.
      apply (cp_eb_W m md data wpl h tab fw eb S CR r3 line c2 ltac:(lia) Hl Hl2 Hlal ltac:(lia) ltac:(lia)
               ltac:(csr; reflexivity) V31' ltac:(csr; reflexivity) ltac:(csr; reflexivity)
               ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)).
      intros r4 c4 AG4 E4 B4. apply (HC r4 c4).
      * eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2]
                                                            | regs_agree_weaken AG3] | regs_agree_weaken AG4].
      * exact E4.
      * csr; reflexivity.
      * lia.
Qed.

(* [comment removed for export] *)
Lemma cp_rows_W : forall m md (data wpl h tab fw eb : Z) (S : TSet), CROW m md data wpl h tab fw eb ->
  forall (n : nat) (r0 r : bvmap 5 word) (i c : Z),
  (0 <= i)%Z -> (Z.of_nat n = h - 1 - i)%Z -> (0 <= c)%Z -> (c + (h - i) * (32 * fw + 32) < 2 ^ 31)%Z ->
  regs_agree (fun x => In x [10; 12; 13; 20; 21; 22; 23; 24; 25; 26; 29; 30; 31]%list) r0 r ->
  getr r 10 = Z_to_bv 64 (data + 4 * wpl * i) -> getr r 29 = Z_to_bv 64 (data + 4 * wpl * i) ->
  getr r 13 = Z_to_bv 64 i -> getr r 11 = Z_to_bv 64 h -> getr r 15 = Z_to_bv 64 (4 * wpl) -> getr r 19 = Z_to_bv 64 wpl ->
  getr r 28 = Z_to_bv 64 1 -> getr r 5 = Z_to_bv 64 fw -> getr r 7 = Z_to_bv 64 fw -> getr r 17 = Z_to_bv 64 eb ->
  getr r 18 = Z_to_bv 64 tab -> getr r 14 = Z_to_bv 64 (2 ^ 64 - 1 - tab) -> getr r 16 = Z_to_bv 64 0 -> getr r 12 = Z_to_bv 64 c ->
  (forall (r' : bvmap 5 word) (c' : Z), regs_agree (fun x => In x [10; 12; 13; 20; 21; 22; 23; 24; 25; 26; 29; 30; 31]%list) r0 r' ->
     getr r' 12 = Z_to_bv 64 c' -> getr r' 13 = Z_to_bv 64 (h - 1) ->
     getr r' 10 = Z_to_bv 64 (data + 4 * wpl * (h - 1)) -> getr r' 29 = Z_to_bv 64 (data + 4 * wpl * (h - 1)) ->
     getr r' 30 = Z_to_bv 64 1 -> (0 <= c' < 2 ^ 31)%Z ->
     realizes SEGS (mkCfg (mkst r' (0x7ea70 : word) m al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0x7e884 : word) m al_rom) md) S.
Proof.
  intros m md data wpl h tab fw eb S CR. pose proof CR as [MP TB RD Hd Hdal Htop Ht Ht2 Htal Hh Hwpl Hfw Heb Hfe Hf0 Hcnt].
  induction n as [|n IH]; intros r0 r i c Hi Hn Hc Hb AG R10 R29 R13 R11 R15 R19 R28 R5 R7 R17 R18 R14 R16 R12 HC.
  all: destruct (cnt_line data wpl h i ltac:(lia) ltac:(lia)) as [Hl1 Hl2].
  all: assert (Hr : (0 <= (h - 1 - i) * (32 * fw + 32))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  all: assert (Hlal : ((data + 4 * wpl * i) mod 4 = 0)%Z) by (rewrite <- Z.mul_assoc; apply cnt_m4; exact Hdal).
  all: apply (cp_row_W m md data wpl h tab fw eb S CR r (data + 4 * wpl * i) c Hl1 Hl2 Hlal Hc ltac:(lia)
                R10 R29 R28 R5 R7 R17 R18 R14 R16 R12).
  all: intros r1 c1 AG1 E1 V30 B1.
  - assert (Ei : i = (h - 1)%Z) by lia. subst i.
    apply (HC r1 c1).
    + eapply regs_agree_trans; [exact AG | regs_agree_weaken AG1].
    + exact E1.
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + exact V30.
    + lia.
  - destruct (cp_Nn al_rom r1 m i h wpl (data + 4 * wpl * i) Hi ltac:(lia) ltac:(lia) Hwpl ltac:(lia) ltac:(lia)
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) V30)
      as (r2 & RUN2 & V13 & V10 & V29 & AG2).
    rzp MP RUN2.
    apply (IH r0 r2 (i + 1)%Z c1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(eapply regs_agree_trans; [eapply regs_agree_trans; [exact AG | regs_agree_weaken AG1] | regs_agree_weaken AG2])
             ltac:(rewrite V10; f_equal; lia) ltac:(rewrite V29; f_equal; lia) V13
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) HC).
Qed.


(* [comment removed for export] *)
Theorem pixCountPixels_W : forall C A m md regs (s pixs pc rc w h cm datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CNT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 pc -> getr regs 12 = Z_to_bv 64 0 -> (s <= pc)%Z -> (pc + 4 <= c_top C)%Z ->
  (pc mod 4 = 0)%Z ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> (1 <= w <= 20000)%Z -> (1 <= h <= 20000)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (2 ^ 17 <= bR)%Z ->
  (forall A' m' vm' regs' (wv : word), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> (forall q, live A' q = live A q) ->
     POSTM C A s (CNTM m pc wv) m' -> getr regs' 10 = Z_to_bv 64 0 -> aroom A' vm' (kR - 1) (bR - 2 ^ 17) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x7e6fc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs pc rc w h cm datas ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hpc Hpc2 ALpc PX Hw Hh Lp Ld
    kR bR Hrm HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof (u64_range (c_sp0 C)) as Usp.
  unfold CNT_STACK, CALLOC_STACK, ALLOC_STACK, LSF in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Hdat. cbn [p_data hdvr] in Hdat.
  pose proof (O23LeptRb2W.rbw_wpl1 w Hw) as Hwpl. pose proof (O23LeptRb2W.rbw_pos (wpl_of w 1) h ltac:(lia) ltac:(lia)) as Hkd.
  destruct (cnt_wdiv w Hw) as (Dfw & Deb & Dfe & Df0 & D625).
  destruct (cp_facts C A m md _ 64 CK HW Lp ltac:(lia)) as (Gp & TOPp & ALp). rewrite u_Z2bv in Gp, TOPp, ALp by lia.
  destruct (cp_facts C A m md _ _ CK HW Ld Hkd) as (Gd & TOPd & ALd). rewrite u_Z2bv in Gd, TOPd, ALd by lia.
  assert (ALp8 : (pixs mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pixs); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  assert (ALd4 : (datas mod 4 = 0)%Z) by (rewrite <- (Z.add_0_r datas); apply mod16_plus_mod4; [exact ALd | reflexivity]).
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (W_sok_win C A m md pc 4 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKc.
  destruct (cnt_entry C A m md regs s pc ret CK HW ltac:(lia) Hpc Hpc2 ltac:(lia) ltac:(lia)) as (HW1 & PM1 & CE1).
  assert (PX1 : PIXat (MCP_A m s pc ret regs) pixs (hdvr rc w h 1 cm datas)).
  { apply (O23LeptRb2W.rbw_PIX_livk A (CNTM0 m pc)); [exact (proj2 PM1) | exact Lp |].
    apply (PIXat_frame m); [exact PX|]. intros x Hx. unfold CNTM0.
    apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  destruct (cp_A al_rom regs m s pixs pc (hdvr rc w h 1 cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) PX ltac:(lia) eq_refl Hpc
              ltac:(lia) ALpc ALp8 SOK SOKc H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q9 & Q20 & Q8 & Q18 & Q19 & AG1).
  rzm HW RUN1.
  assert (P4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A (MCP_A m s pc ret regs) md r1 256 4 kR bR (Z_to_bv 64 0x7e778) (s - 112) S CK HW1 Q10 Q11
           ltac:(lia) ltac:(lia) ltac:(lia) Hrm HkR ltac:(rewrite alloc_margin_small by lia; lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) P4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m3 vm1 r3 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrm1.
  replace (Z_to_bv 64 0x7e778) with (0x7e778 : word) by (apply bv_eq; reflexivity).
  change (256 * 4)%Z with 1024%Z in L1, Hrm1.
  pose proof (u64_range res) as Ures.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (tab := u res) in *. clearbody tab.
  rewrite Eres in Hres, L0, L1, L00, LEQ.
  clear ZERO TOP Hnz.
  destruct (cp_facts C A1 m3 _ _ 1024 CK HWa L1 ltac:(lia)) as (Gt & TOPt & _). rewrite u_Z2bv in Gt, TOPt by lia.
  assert (ALt4 : (tab mod 4 = 0)%Z) by (rewrite <- (Z.add_0_r tab); apply mod16_plus_mod4; [exact AL16 | reflexivity]).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  pose proof (cellsZ_frm C (s - 112) _ m3 (CPC s ret regs) CK (proj1 PMa) ltac:(lia) ltac:(unfold CPC; fa12) CE1) as CE3.
  pose proof (O23LeptRb2W.rbw_PIX_livk A _ m3 pixs _ (proj2 PMa) Lp PX1) as PX3.
  destruct (cp_T0 al_rom r3 m3 tab ltac:(lia) ltac:(lia) ALt4 Hres) as (r4 & RUN4 & V18 & V10 & V11 & V12 & V13 & V14 & AG4).
  rzm HWa RUN4.
  apply (cp_tab_W C A A1 _ m3 s tab S CK SUBa L1 L0 L00 ltac:(lia) ltac:(lia) ALt4 255 r4 r4 m3 0 HWa (POSTM_refl _ _ _ _)
           ltac:(intros a _; reflexivity) ltac:(intros j Hj; exfalso; lia) ltac:(lia) ltac:(reflexivity) (regs_agree_refl _ _)
           V18 V11 V12 V10 ltac:(rewrite V13; f_equal; lia) ltac:(rewrite V14; f_equal; lia) ltac:(csr; reflexivity)).
  intros m4 r5 HW4 PM4 FT4 TB4 AG5. unfold FTc in FT4.
  assert (NEpt : Z_to_bv 64 pixs <> Z_to_bv 64 tab) by (intros E; rewrite E in Lp; rewrite Lp in L0; discriminate).
  pose proof (V23LeptCmap2.blk_apart C A1 m3 _ _ _ _ _ CK HWa (SUBa _ _ Lp) L1 NEpt ltac:(lia) ltac:(lia)) as APpt.
  rewrite !u_Z2bv in APpt by lia.
  assert (PX4 : PIXat m4 pixs (hdvr rc w h 1 cm datas)) by (apply (PIXat_frame m3); [exact PX3 | intros x Hx; apply FT4; lia]).
  pose proof (cellsZ_out m3 m4 tab (tab + 1024) (CPC s ret regs) FT4 ltac:(unfold CPC; fa12) CE3) as CE4.
  pose proof (W_sok_win C A1 m4 _ (s - 112) 112 CK HW4 ltac:(lia) ltac:(cbn; lia)) as SOK4.
  destruct (cp_B al_rom r5 m4 s pixs tab (hdvr rc w h 1 cm datas) ltac:(lia) ltac:(lia) Hs16 ltac:(lia) PX4 ltac:(lia) ALp8
              ltac:(cbn [p_w hdvr]; lia) ltac:(cbn [p_h hdvr]; lia) ltac:(cbn [p_wpl hdvr]; lia) ltac:(cbn [p_data hdvr]; lia)
              ltac:(cbn [p_data hdvr]; exact ALd4) ltac:(lia) ltac:(lia) SOK4 ltac:(csr; reflexivity) ltac:(csr; reflexivity)
              ltac:(csr; reflexivity))
    as (r6 & RUN6 & B10 & B29 & B19 & B11 & B12 & B13 & B5 & B7 & B17 & B14 & B15 & B16 & B28 & AG6).
  cbn [p_w p_h p_wpl p_data hdvr] in RUN6, B10, B29, B19, B11, B5, B7, B17, B15.
  rzm HW4 RUN6.
  assert (WP5 : W C A1 (DIMC m4 s w h) (with_vmmaps vm1 md) /\ POSTM C A s m4 (DIMC m4 s w h)) by (unfold DIMC; wp_win CK).
  destruct WP5 as [HW5 PM5].
  assert (OUT5 : forall x : word, ~ (s - 104 <= u x < s - 96)%Z -> DIMC m4 s w h x = m4 x).
  { intros x Hx. unfold DIMC. rewrite !wbytes_outside.
    all: first [ reflexivity | (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ]. }
  pose proof (cellsZ_out m4 _ (s - 104) (s - 96) (CPC s ret regs) OUT5 ltac:(unfold CPC; fa12) CE4) as CE5.
  assert (TB5 : TAB8 (DIMC m4 s w h) tab) by (apply (cnt_tab8_frame m4); [lia | lia | exact TB4 | intros x Hx; apply OUT5; lia]).
  pose proof (SUBa _ _ Ld) as Ld1.
  assert (Hcnt : (h * (32 * (w / 32) + 32) < 2 ^ 31)%Z).
  { assert (h * (32 * (w / 32) + 32) <= 20000 * (32 * 625 + 32))%Z by (apply Z.mul_le_mono_nonneg; lia). lia. }
  assert (CR : CROW (DIMC m4 s w h) (with_vmmaps vm1 md) datas (wpl_of w 1) h tab (w / 32) (w mod 32)).
  { constructor; try lia.
    - exact (w_pure _ _ _ _ HW5).
    - exact TB5.
    - intros a Ha1 Ha2.
      destruct (V23LeptRot90cwW.r90w_rd4_blk C A1 _ _ _ _ a CK HW5 Ld1 ltac:(rewrite u_Z2bv by lia; lia)
                  ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as (bs & ? & R & _).
      exists bs. exact R. }
  apply (cp_rows_W _ _ datas (wpl_of w 1) h tab (w / 32) (w mod 32) S CR (Z.to_nat (h - 1)) r6 r6 0 0 ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) (regs_agree_refl _ _)); try (csr; first [reflexivity | (f_equal; lia)]).
  intros r7 c7 AG7 E12 E13 E10 E29 E30 Bc.
  pose proof (W_sok_win C A1 _ _ pc 4 CK HW5 ltac:(lia) ltac:(cbn; lia)) as SOKc5.
  assert (Hlh : (0 <= wpl_of w 1 * (h - 1))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (cp_Nx al_rom r7 (DIMC m4 s w h) (h - 1) (wpl_of w 1) (datas + 4 * wpl_of w 1 * (h - 1)) pc tab c7 ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bc SOKc5 E13 ltac:(csr; f_equal; lia) E10 E29
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) E30 ltac:(csr; reflexivity) ltac:(csr; reflexivity)
              ltac:(csr; reflexivity) E12)
    as (r8 & RUN8 & X1 & X10 & AG8).
  rzm HW5 RUN8.
  assert (HW6 : W C A1 (wbytes (DIMC m4 s w h) (Z_to_bv 64 pc) (word_to_le_bytes 4 (Z_to_bv 64 c7))) (with_vmmaps vm1 md)).
  { apply (W_store_win C A1 _ _ _ _ CK HW5); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  assert (PM6 : POSTM C A s (CNTM m pc (Z_to_bv 64 c7)) (wbytes (DIMC m4 s w h) (Z_to_bv 64 pc) (word_to_le_bytes 4 (Z_to_bv 64 c7)))).
  { unfold CNTM. apply cnt_postm_cell.
    eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [eapply POSTM_mono; [|exact PMa]; lia|].
    eapply POSTM_trans; [exact PM4 | exact PM5]. }
  assert (CE6 : cellsZ (wbytes (DIMC m4 s w h) (Z_to_bv 64 pc) (word_to_le_bytes 4 (Z_to_bv 64 c7))) (CPC s ret regs)).
  { apply (cellsZ_out (DIMC m4 s w h) _ pc (pc + 4)); [| unfold CPC; fa12 | exact CE5].
    intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  replace (0x10e818 : word) with (Z_to_bv 64 0x10e818) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 _ _ r8 (Z_to_bv 64 tab) (Z_to_bv 64 0x7eb84) 1024 (s - 112) S CK HW6 X10 L1 L00 X1
           ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m7 vm2 r9 HW7 CS9 L2t LEQ2 PM7 RT.
  rewrite with_vmmaps_twice in HW7 |- *.
  replace (Z_to_bv 64 0x7eb84) with (0x7eb84 : word) by (apply bv_eq; reflexivity).
  pose proof (cellsZ_frm C (s - 112) _ m7 (CPC s ret regs) CK (proj1 PM7) ltac:(lia) ltac:(unfold CPC; fa12) CE6) as CE7.
  unfold CPC in CE7.
  destruct (cp_F al_rom r9 m7 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) ltac:(lia) ltac:(lia) Hret CE7
              ltac:(csr; reflexivity))
    as (r10 & RUN10 & F2 & F1 & F10 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & AG10).
  rzm HW7 RUN10.
  assert (LIV : forall q, live A2 q = live A q).
  { intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 tab)) as [->|NE].
    - rewrite L2t, L0. reflexivity.
    - rewrite (LEQ2 q NE), (LEQ q NE). reflexivity. }
  apply (HK A2 m7 vm2 r10 (Z_to_bv 64 c7) HW7).
  - apply cs_kept_intro; csr; reflexivity.
  - exact LIV.
  - eapply POSTM_trans; [exact PM6|]. apply (POSTM_sub C A A2); [apply sub_live_eq; exact LIV|].
    eapply POSTM_mono; [|exact PM7]; lia.
  - exact F10.
  - rewrite with_vmmaps_vmmaps in RT. rewrite alloc_margin_small in Hrm1 by lia.
    pose proof (RT _ _ Hrm1 ltac:(lia) ltac:(lia)) as X. rewrite !Z.sub_0_r in X. exact X.
Qed.
End CountW.
