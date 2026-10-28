(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptPixaCreate V2_code_pixaAddPix.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
Definition PIXAADD_STOPS : list Z := []%Z.
Definition PIXAADD_FDEF : list (nat * nat) := [].

(* [comment removed for export] *)
Ltac exB_sc_hook ::=
  repeat match goal with H : alu64 ALU_ADD _ _ = Z_to_bv 64 _ |- _ => rewrite !H end;
  repeat rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ]);
  first [ (rewrite ?alu_xor, ?alu_sltu, ?alu_slt; rewrite exB_ovf_idiom by lia; reflexivity)
        | (rewrite ?w_addw; rewrite ?zbv_addw_small by lia; ex_br) ].

Ltac pxs EA SOK := rewrite ?EA; rewrite ?zbv_addi, ?Z.add_0_r; first [ exact SOK | (rewrite ?u_Z2bv by lia; lia) ].

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Lemma pixaAdd_run : forall (fx : FPState) regs (m : word -> option byte) (s pa parr pix n : Z) (ret : word),
  (4096 + 48 <= s <= 2 ^ 47)%Z -> (4096 <= pa)%Z -> (pa + 32 <= 2 ^ 47)%Z -> (4096 <= parr)%Z -> (parr + 80 <= 2 ^ 47)%Z -> (0 <= n < 10)%Z -> (1 <= pix < 2 ^ 47)%Z ->
  (pa + 32 <= s - 48 \/ s <= pa)%Z -> (parr + 80 <= s - 48 \/ s <= parr)%Z -> (parr + 80 <= pa \/ pa + 32 <= parr)%Z -> (pa mod 16 = 0)%Z -> (parr mod 16 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 n) -> rdn SEGS m (Z_to_bv 64 (pa + 4)) 4 = Some (Z_to_le_bytes 4 10) ->
  rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pa) 4 = true -> store_ok SEGS m (Z_to_bv 64 (parr + 8 * n)) 8 = true ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pa -> getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x18450) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom
      /\ rinv [((s - 48)%Z, 48%Z); ((parr + 8 * n)%Z, 8%Z); (pa, 4%Z)] m M'
      /\ rdn SEGS M' (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 (n + 1)) /\ rdn SEGS M' (Z_to_bv 64 (parr + 8 * n)) 8 = Some (Z_to_le_bytes 8 pix)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs').
Proof.
  intros fx regs m s pa parr pix n ret Hs Hpa Hpa47 Hparr Hparr47 Hn Hpix Dpa Dparr Dpp ALpa ALparr Rn R4 R16 SOK SOKpa SOKsl
    H1 Hret H2 H10 H11 H12.
  assert (EA : alu64 ALU_ADD (Z_to_bv 64 parr) (mul_div M_MUL (Z_to_bv 64 8) (ext_val true 0 4 (Z_to_bv 64 n))) = Z_to_bv 64 (parr + 8 * n)).
  { rewrite ex_sx32 by lia. rewrite m_mul, zbv_mul, alu_add, zbv_add. reflexivity. }
  ex_entry regs [s; pa; parr; pix; n] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pa; parr; pix; n]) m
     [KWr (SA (EVar 32) (-48)) 48; KWr (SA (EVar 33) 0) 4;
      KRange (EVar 32) 4144 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47 - 32); KRange (EVar 34) 4096 (2 ^ 47 - 80);
      KRange (EVar 35) 1 (2 ^ 47 - 1); KRange (EVar 36) 0 9; KAlign (EVar 33) 16; KAlign (EVar 34) 16;
      KWord (SA (EVar 33) 0) 4 (EVar 36); KWord (SA (EVar 33) 4) 4 (ELit 10); KWord (SA (EVar 33) 16) 8 (EVar 34);
      KDisj (SA (EVar 33) 0) 32 (SA (EVar 32) (-48)) 48]) by (ex_know regs).
  ex_open HR HK Hms Hlf.
  ex_cont 100%nat [0x18670%Z] (SCR [false; false] [] []) HR Hlf HK Hms.
  all: lazymatch goal with |- reach _ _ _ => idtac | _ => pxs EA SOKsl end.
  assert (HRA : getr R 1%bv = ret) by (rewrite (reg_val _ _ _ 1%bv HR); vm_compute sr_get; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; exact H1).
  eapply reach_msteps; [exact Hms|].
  unfold reach. eexists. split.
  - norm_pc. stepret F_18670 D_18670 ret ltac:(exact HRA). apply mst_refl.
  - do 2 eexists. split; [reflexivity|].
    split; [exB_rinv_tac Hlf [((s - 48)%Z, 48%Z); ((parr + 8 * n)%Z, 8%Z); (pa, 4%Z)]; exB_reg_tac ltac:(rewrite ?EA)|].
    split.
    { exB_cell HK Hlf (EVar 33) 0%Z 4%nat pa (n + 1)%Z Hc1 idtac idtac idtac.
      - exB_scs regs.
      - exB_tacA idtac.
      - exB_tacV idtac.
      - exact Hc1. }
    split.
    { exB_cell HK Hlf (EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 8) (EExt true 0 4 (EVar 36)))) 0%Z 8%nat (parr + 8 * n)%Z pix Hc2 idtac idtac idtac.
      - exB_scs regs. all: pxs EA SOKsl.
      - exB_tacA ltac:(rewrite EA).
      - exB_tacV idtac.
      - exact Hc2. }
    repeat match goal with |- _ /\ _ => split end.
    all: first [ ex_reg regs HR | ex_agree HRo HR ].
Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PixaAddW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.

Lemma pxa_sok_blk : forall C A m md (p k a : Z) (n : nat), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some k ->
  (0 <= p)%Z -> (p + k < 2 ^ 64)%Z -> (p <= a)%Z -> (a + Z.of_nat n <= p + k)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hp Hpk Hlo Hhi.
  apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md (Z_to_bv 64 p) k x CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E).
Qed.

Ltac pxa_notin := let X := fresh "X" in intros X; cbn [In] in X;
  repeat (destruct X as [X|X]; [apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X|]); exact X.

Lemma pixaAddPix_ins_W : forall (fx : FPState) C Ar A m md regs (s pa parr ba barr n pix : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 48 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pa -> getr regs 11 = Z_to_bv 64 pix -> getr regs 12 = Z_to_bv 64 0 ->
  pixa_cells m pa parr ba barr n -> (0 <= n < 10)%Z -> pixa_blks C A pa parr ba barr ->
  live Ar (Z_to_bv 64 pa) = None -> live Ar (Z_to_bv 64 parr) = None -> (1 <= pix < 2 ^ 47)%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     (forall a : word, ~ (s - 48 <= u a < s)%Z -> ~ (parr + 8 * n <= u a < parr + 8 * n + 8)%Z -> ~ (pa <= u a < pa + 4)%Z -> m' a = m a) ->
     pixa_cells m' pa parr ba barr (n + 1) -> rdn SEGS m' (Z_to_bv 64 (parr + 8 * n)) 8 = Some (Z_to_le_bytes 8 pix) ->
     getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 0x18450) m al_rom) md) S.
Proof.
  intros fx C Ar A m md regs s pa parr ba barr n pix ret S CK HW SUB H2 Hlo Hhi H1 Hret H10 H11 H12 PC Hn PB LpaR LparrR Hpix HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as HLS.
  destruct PB as (Gpa & Gparr & Gba & Gbarr & Lpa & Lparr & Lba & Lbarr & L0pa & L0parr & L0ba & L0barr).
  destruct PC as (Rn & R4 & R8 & R16 & R24 & Rb0 & Rb4 & Rb8 & Rb16).
  pose proof (blk_range C A m md _ 32 CK HW Lpa ltac:(lia)) as [Ba1 Ba2].
  pose proof (blk_range C A m md _ 80 CK HW Lparr ltac:(lia)) as [Bb1 Bb2].
  pose proof (blk_range C A m md _ 24 CK HW Lba ltac:(lia)) as [Bc1 Bc2].
  rewrite u_Z2bv in Ba1, Ba2, Bb1, Bb2, Bc1, Bc2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpa) as (_ & ALpa & _).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lparr) as (_ & ALparr & _).
  rewrite u_Z2bv in ALpa, ALparr by lia.
  assert (DISJ : forall (p k q j : Z), live A (Z_to_bv 64 p) = Some k -> live A (Z_to_bv 64 q) = Some j ->
            (0 <= p < 2 ^ 64)%Z -> (0 <= q < 2 ^ 64)%Z -> Z_to_bv 64 p <> Z_to_bv 64 q -> (p + k <= q \/ q + j <= p)%Z).
  { intros p k q j Lp Lq Hp Hq NE.
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (Kp & _).
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lq) as (Kq & _).
    pose proof (round16_ge k Kp). pose proof (round16_ge j Kq).
    destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
  assert (Dpp : (pa + 32 <= parr \/ parr + 80 <= pa)%Z) by (apply DISJ; try assumption; intros E; rewrite E in Lpa; congruence).
  assert (Dbp : (ba + 24 <= pa \/ pa + 32 <= ba)%Z) by (apply DISJ; try assumption; intros E; rewrite E in Lba; congruence).
  assert (Dbr : (ba + 24 <= parr \/ parr + 80 <= ba)%Z) by (apply DISJ; try assumption; intros E; rewrite E in Lba; congruence).
  rewrite Z.add_0_r in Rn.
  pose proof (pixaAdd_run al_rom fx regs m s pa parr pix n ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hn Hpix
                ltac:(lia) ltac:(lia) ltac:(lia) ALpa ALparr Rn R4 R16
                (W_sok_win C A m md (s - 48)%Z 48 CK HW ltac:(lia) ltac:(lia))
                (pxa_sok_blk C A m md pa 32 pa 4 CK HW Lpa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
                (pxa_sok_blk C A m md parr 80 (parr + 8 * n) 8 CK HW Lparr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
                H1 Hret H2 H10 H11 H12) as RUN.
  apply (rz_reach SEGS _ md _ S (w_pure _ _ _ _ HW) RUN).
  intros fin (regs' & M' & -> & RI & Rn' & Rp' & R10' & R2' & AG).
  assert (WP : W C A M' md /\ POSTM C Ar s m M').
  { apply (rinv_WP2 C Ar A m md M' _ s CK HW SUB Hhi RI).
    unfold local_regions. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - left. lia.
    - right. exists (Z_to_bv 64 parr), 80%Z. rewrite u_Z2bv by lia.
      split; [exact Lparr|]. split; [exact LparrR|]. split; [exact L0parr|]. lia.
    - right. exists (Z_to_bv 64 pa), 32%Z. rewrite u_Z2bv by lia.
      split; [exact Lpa|]. split; [exact LpaR|]. split; [exact L0pa|]. lia. }
  destruct WP as [HW' PM'].
  assert (KEEP : forall (z : Z) (k : nat), (0 <= z)%Z -> (z + Z.of_nat k <= 2 ^ 64)%Z -> (z + Z.of_nat k <= s - 48 \/ s <= z)%Z ->
            (z + Z.of_nat k <= parr + 8 * n \/ parr + 8 * n + 8 <= z)%Z -> (z + Z.of_nat k <= pa \/ pa + 4 <= z)%Z ->
            rdn SEGS M' (Z_to_bv 64 z) k = rdn SEGS m (Z_to_bv 64 z) k).
  { intros z k Z1 Z2 Z3 Z4 Z5. apply (rinv_rdn SEGS _ _ _ z k RI Z1 Z2).
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr. }
  apply (HK M' regs' HW').
  - apply cs_kept_intro; apply AG; pxa_notin.
  - exact PM'.
  - intros a A1 A2 A3. apply (proj2 RI). intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<-|Hr]; [unfold inreg; cbn [fst snd]; lia|]). destruct Hr.
  - unfold pixa_cells.
    split; [rewrite Z.add_0_r; exact Rn'|].
    split; [rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R4|].
    split; [rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R8|].
    split; [rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R16|].
    split; [rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact R24|].
    split; [rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rb0|].
    split; [rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rb4|].
    split; [rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rb8|].
    rewrite KEEP by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact Rb16.
  - exact Rp'.
  - exact R10'.
Qed.
End PixaAddW.
