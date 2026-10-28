(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB LeptCellsB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptBl_iface V2LeptBilCSegs.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Lemma str_bc_msg : str16 0x12528 14.
Proof. str16_tac. Qed.
Lemma str_bc_proc : str16 0x10a26 15.
Proof. str16_tac. Qed.

Section BilCW1.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Hypothesis H_amb : forall fx : FPState, @pixAddMirroredBorder_contract fx AL CL ASR.
Hypothesis H_gev : forall fx : FPState, @pixGetExtremeValue_contract fx AL CL ASR.

Definition BC_WIN : Z := 5120.
(* [comment removed for export] *)
Definition bc_saved (regs fr : bvmap 5 word) : list cell := [(312%Z, 8%nat, u (getr regs 1)); (304%Z, 8%nat, u (getr regs 8)); (296%Z, 8%nat, u (getr regs 9)); (288%Z, 8%nat, u (getr regs 18)); (280%Z, 8%nat, u (getr regs 19)); (272%Z, 8%nat, u (getr regs 20)); (264%Z, 8%nat, u (getr regs 21)); (256%Z, 8%nat, u (getr regs 22)); (248%Z, 8%nat, u (getr regs 23)); (240%Z, 8%nat, u (getr regs 24)); (232%Z, 8%nat, u (getr regs 25)); (224%Z, 8%nat, u (getr regs 26)); (216%Z, 8%nat, u (getr regs 27)); (208%Z, 8%nat, u (Z_to_bv 64 (u (reg_get fr 8)))); (200%Z, 8%nat, u (Z_to_bv 64 (u (reg_get fr 9)))); (192%Z, 8%nat, u (Z_to_bv 64 (u (reg_get fr 18))))].
Definition bc_fl1 (regs fr : bvmap 5 word) (bsc minv maxv : Z) : list cell :=
  bc_saved regs fr ++ [(24%Z, 8%nat, bsc); (32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z); (172%Z, 4%nat, minv); (168%Z, 4%nat, maxv)].
(* [comment removed for export] *)
Lemma fs_notin_A : forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> ~ In (ridx r) [8; 9; 13; 14; 15]%nat.
Proof.
  intros r Hr N8 N9 Hin. unfold fs_list in Hr. unfold ridx in Hin. cbn [In] in Hr, Hin.
  assert (U : bv_unsigned r = 8%Z \/ bv_unsigned r = 9%Z) by lia.
  destruct U as [U|U]; [apply N8 | apply N9]; apply bv_eq; rewrite U; reflexivity.
Qed.
Lemma fs_notin_V : forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> ~ In (ridx r) [8; 9; 18]%nat.
Proof.
  intros r N8 N9 N18 Hin. unfold ridx in Hin. cbn [In] in Hin.
  assert (U : bv_unsigned r = 8%Z \/ bv_unsigned r = 9%Z \/ bv_unsigned r = 18%Z) by lia.
  destruct U as [U|[U|U]]; [apply N8 | apply N9 | apply N18]; apply bv_eq; rewrite U; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma W_clr_got : forall C A m md, W C A m md -> forall j, (0x44e98 <= j < 0x44e98 + 8)%Z -> m (Z_to_bv 64 j) = None.
Proof.
  intros C A m md HW j Hj.
  apply (exW_clr_None C A m md 0x44e98 (0x44e98 + 8) 0x44e40 0x44ee0 HW); [cbv [ll_clr LLU16]; cbn [In]; auto | lia | lia | lia | lia | exact Hj].
Qed.
Lemma W_clr_sev : forall C A m md, W C A m md -> forall j, (0x45f08 <= j < 0x45f08 + 4)%Z -> m (Z_to_bv 64 j) = None.
Proof.
  intros C A m md HW j Hj.
  apply (exW_clr_None C A m md 0x45f08 (0x45f08 + 4) 0x45f08 0x45f10 HW); [cbv [ll_clr LLU16]; cbn [In]; auto | lia | lia | lia | lia | exact Hj].
Qed.

Local Ltac zlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Lemma bc_u64 : forall x : word, (0 <= bv_unsigned x < 2 ^ 64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

Lemma bc_w2b : forall (k : nat) (x : word), word_to_le_bytes k x = Z_to_le_bytes k (bv_unsigned x).
Proof. intros k x. rewrite <- (w2b_Z k (bv_unsigned x)) by apply bc_u64. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma bc_m16_4 : forall x, (x mod 16 = 0)%Z -> (x mod 4 = 0)%Z.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (4 * q)%Z. ring. Qed.

Lemma bc_m16_8 : forall x, (x mod 16 = 0)%Z -> (x mod 8 = 0)%Z.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (2 * q)%Z. ring. Qed.

Lemma bc_msub : forall x k d, (d <> 0)%Z -> (x mod d = 0)%Z -> (k mod d = 0)%Z -> ((x - k) mod d = 0)%Z.
Proof.
  intros x k d Hd Hx Hk. apply Z.mod_divide in Hx; [|exact Hd]. apply Z.mod_divide in Hk; [|exact Hd].
  apply Z.mod_divide; [exact Hd|]. destruct Hx as [a ->]. destruct Hk as [b ->]. exists (a - b)%Z. ring.
Qed.

Lemma bc_livk_at : forall A m m' (p k : Z) (x : word), LIVK A m m' -> live A (Z_to_bv 64 p) = Some k ->
  (0 <= p)%Z -> (p + k < 2 ^ 64)%Z -> (p <= u x < p + k)%Z -> m' x = m x.
Proof.
  intros A m m' p k x L Hl H0 H1 Hx.
  pose proof (L (Z_to_bv 64 p) k (u x - p)%Z Hl ltac:(lia)) as E. unfold at_ in E.
  rewrite u_Z2bv in E by lia. replace (p + (u x - p))%Z with (u x) in E by lia.
  rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Lemma bc_rdn_keep : forall m m' (x : Z) (n : nat), (0 <= x)%Z -> (x + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall a : word, (x <= u a < x + Z.of_nat n)%Z -> m' a = m a) ->
  rdn SEGS m' (Z_to_bv 64 x) n = rdn SEGS m (Z_to_bv 64 x) n.
Proof.
  intros m m' x n H0 H1 H.
  apply (agree_rdn SEGS x (Z.of_nat n) m m' x n); [intros a Ha _; apply H; exact Ha | lia | lia | lia | lia].
Qed.

Lemma bc_pixr_frame : forall C A A' m m' (pix data : Z) v, pixr_new C A A' m pix data v ->
  (forall x : word, (pix <= u x < pix + 64)%Z -> m' x = m x) -> pixr_new C A A' m' pix data v.
Proof.
  intros C A A' m m' pix data v P F. unfold pixr_new in *.
  destruct P as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16).
  assert (PX : PIXat m' pix v) by (eapply PIXat_frame; [exact Q15 | exact F]).
  exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (conj Q14 (conj PX Q16))))))))))))))).
Qed.

Lemma bc_cs_rest : forall r : reg, AllocIface.callee_saved r -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> In r cs_rest.
Proof.
  intros r CS N2 N8 N9. unfold AllocIface.callee_saved in CS. unfold cs_rest.
  destruct CS as [E|[E|[E|[E|[E|E]]]]]; [contradiction | subst r; cbn [In]; auto | subst r; cbn [In]; auto | contradiction | contradiction |].
  assert (U : bv_unsigned r = 18%Z \/ bv_unsigned r = 19%Z \/ bv_unsigned r = 20%Z \/ bv_unsigned r = 21%Z \/ bv_unsigned r = 22%Z \/
              bv_unsigned r = 23%Z \/ bv_unsigned r = 24%Z \/ bv_unsigned r = 25%Z \/ bv_unsigned r = 26%Z \/ bv_unsigned r = 27%Z) by lia.
  cbn [In].
  destruct U as [U|[U|[U|[U|[U|[U|[U|[U|[U|U]]]]]]]]]; repeat (first [left; apply bv_eq; rewrite U; reflexivity | right]).
Qed.

Lemma bc_cells_A : forall m (s : Z) (regs fr : bvmap 5 word),
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 8)))) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 9)))) ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (reg_get fr 18)))) ->
  rdn SEGS m (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10) ->
  rdn SEGS m (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11) ->
  cellsAt SEGS m (s - 320) (bc_saved regs fr ++ [(32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z)]).
Proof.
  intros. unfold cellsAt, bc_saved. cbn [app].
  repeat apply Forall_cons; cbn [c_off c_len c_val fst snd]; try apply Forall_nil.
  all: match goal with |- rdn _ _ (Z_to_bv 64 (?sv - 320 + ?o)) _ = _ =>
         let k := eval vm_compute in (320 - o)%Z in replace (sv - 320 + o)%Z with (sv - k)%Z by lia end.
  all: first [assumption | rewrite <- bc_w2b; assumption].
Qed.

Lemma bc_cells_fl1 : forall m (s : Z) (regs fr : bvmap 5 word) (bsc minv maxv : Z),
  cellsAt SEGS m (s - 320) (bc_saved regs fr ++ [(32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z)]) ->
  rdn SEGS m (Z_to_bv 64 (s - 296)) 8 = Some (Z_to_le_bytes 8 bsc) ->
  rdn SEGS m (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
  cellsAt SEGS m (s - 320) (bc_fl1 regs fr bsc minv maxv).
Proof.
  intros m s regs fr bsc minv maxv H R24 R172 R168.
  unfold cellsAt, bc_fl1 in *. apply Forall_app in H as [HS HX].
  apply Forall_app. split; [exact HS|].
  pose proof (Forall_inv HX) as X32. pose proof (Forall_inv (Forall_inv_tail HX)) as X48.
  cbn [c_off c_len c_val fst snd] in X32, X48.
  repeat apply Forall_cons; cbn [c_off c_len c_val fst snd]; try apply Forall_nil.
  - replace (s - 320 + 24)%Z with (s - 296)%Z by lia. exact R24.
  - exact X32.
  - exact X48.
  - replace (s - 320 + 172)%Z with (s - 148)%Z by lia. exact R172.
  - replace (s - 320 + 168)%Z with (s - 152)%Z by lia. exact R168.
Qed.

Lemma bc_mid : forall fr1 cs1 C A m md r (s pixs bsc : Z) (v : pixv) (S : TSet),
  Cok C -> W C A m md -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> (s mod 16 = 0)%Z ->
  getr r 2 = Z_to_bv 64 (s - 320) -> getr r 10 = Z_to_bv 64 bsc -> (0 <= bsc < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs) -> bl_src A m pixs v ->
  (forall m' r' (minv maxv : Z), W C A m' md -> (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z ->
     rdn SEGS m' (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv) ->
     rdn SEGS m' (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv) ->
     agree_win (s - 320) 320 [(168%Z, 4%Z); (172%Z, 4%Z)] m m' ->
     (forall a : word, ~ (c_top C - LSTK <= u a < s)%Z -> m' a = m a) ->
     getr r' 2 = Z_to_bv 64 (s - 320) -> getr r' 8 = Z_to_bv 64 5 -> getr r' 9 = Z_to_bv 64 bsc ->
     (forall x, In x cs_rest -> getr r' x = getr r x) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r' (Z_to_bv 64 0x399fc) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r (Z_to_bv 64 0x399b0) m al_rom) md) S.
Proof.
  intros fr1 cs1 C A m md r s pixs bsc v S CK HW Hstk Htop Hs16 H2 H10 Hb R160 SRC K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  pose proof SRC as (PX & _ & _ & _ & _ & _ & _ & Lp & _).
  pose proof PX as (Hp0 & Hp64 & _).
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  pose proof (bc_m16_4 s Hs16) as Hs4.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | exact (bc_B al_rom (mkFP fr1 cs1) r m s pixs bsc ltac:(lia) ltac:(lia) R160 H2 Hb H10) |].
  intros fin (rB & MB & -> & -> & B1 & B2 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B9 & AGB).
  refine (H_gev (mkFP fr1 cs1) C A m md rB (s - 320)%Z pixs 4%Z (s - 148)%Z v (Z_to_bv 64 0x399d8) S CK HW B2
            (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl) ltac:(unfold GEV_STACK; lia) ltac:(lia) ltac:(lia) (bc_msub s 148 4 ltac:(lia) Hs4 eq_refl)
            B1 ltac:(red; apply bv_eq; reflexivity) B10 B11 B12 B13 B14 B15 B16 SRC (or_introl eq_refl) _).
  intros m1 r1 val1 W1 CS1 V1 RD1 FR1.
  assert (PX1 : PIXat m1 pixs v) by (eapply PIXat_frame; [exact PX | intros x Hx; apply FR1; [unfold scratch; lia | lia]]).
  assert (SRC1 : bl_src A m1 pixs v) by (destruct SRC as (_ & Rest); exact (conj PX1 Rest)).
  assert (R160a : rdn SEGS m1 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { rewrite (bc_rdn_keep m m1) by first [zlia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; apply FR1; [unfold scratch; lia | lia]].
    exact R160. }
  eapply rz_reach; [exact (w_pure _ _ _ _ W1) | exact (bc_C al_rom (mkFP fr1 cs1) r1 m1 s pixs ltac:(lia) ltac:(lia) R160a ltac:(csr; reflexivity)) |].
  intros fin (rC & MC & -> & -> & C1 & C2 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C8 & AGC).
  refine (H_gev (mkFP fr1 cs1) C A m1 md rC (s - 320)%Z pixs 5%Z (s - 152)%Z v (Z_to_bv 64 0x399fc) S CK W1 C2
            (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl) ltac:(unfold GEV_STACK; lia) ltac:(lia) ltac:(lia) (bc_msub s 152 4 ltac:(lia) Hs4 eq_refl)
            C1 ltac:(red; apply bv_eq; reflexivity) C10 C11 C12 C13 C14 C15 C16 SRC1 (or_intror eq_refl) _).
  intros m2 r2 val2 W2 CS2 V2 RD2 FR2.
  apply (K m2 r2 val1 val2 W2 V1 V2).
  - rewrite (bc_rdn_keep m1 m2) by first [zlia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; apply FR2; [unfold scratch; lia | lia]].
    exact RD1.
  - exact RD2.
  - intros a Ha HRO.
    pose proof (HRO (168%Z, 4%Z) ltac:(cbn [In]; auto)) as X1. pose proof (HRO (172%Z, 4%Z) ltac:(cbn [In]; auto)) as X2.
    cbn [fst snd] in X1, X2.
    rewrite FR2 by (unfold scratch; lia). apply FR1; [unfold scratch; lia | lia].
  - intros a Ha. rewrite FR2 by (unfold scratch; lia). apply FR1; [unfold scratch; lia | lia].
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - rest_solve.
Qed.

Local Ltac rinv_out RI :=
  apply (proj2 RI); let rr := fresh "rr" in let Hr := fresh "Hr" in
  intros rr Hr; cbn [In] in Hr; unfold inreg; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]); destruct Hr.

(* [comment removed for export] *)
Lemma bc_head_W : forall fr cs C A m md regs (s pixs : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 1 ->
  reg_get fr 10 = Z_to_bv 64 18446744070498811904 -> reg_get fr 11 = Z_to_bv 64 18446744070507200512 ->
  bl_src A m pixs v -> p_rc v = 1%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> (22 <= p_w v)%Z -> (22 <= p_h v)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_amb (p_w v) (p_h v) 11 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_amb (p_w v) (p_h v) 11) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A1 m1 vm1 regs1 (bsc datasc minv maxv : Z), W C A1 m1 (with_vmmaps vm1 md) -> frm_zero cs' -> POSTM C A s m m1 ->
     cellsAt SEGS m1 (s - 320) (bc_fl1 regs fr bsc minv maxv) -> (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z ->
     hdr_ok (p_w v + 2 * 11) (p_h v + 2 * 11) 8 -> pixr_new C A A1 m1 bsc datasc (set_data (pix_hdr (p_w v + 2 * 11) (p_h v + 2 * 11) 8) datasc) ->
     getr regs1 1 = Z_to_bv 64 0x39a18 -> getr regs1 2 = Z_to_bv 64 (s - 320) -> getr regs1 4 = Z_to_bv 64 0x56270 -> getr regs1 10 = Z_to_bv 64 1 ->
     getr regs1 11 = Z_to_bv 64 104 -> getr regs1 9 = Z_to_bv 64 bsc -> getr regs1 22 = Z_to_bv 64 1 -> getr regs1 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 22; 24]%bv -> getr regs1 r = getr regs r) ->
     reg_get fr' 8 = Z_to_bv 64 18446744070507200512 -> reg_get fr' 9 = Z_to_bv 64 18446744070498811904 ->
     (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> reg_get fr' r = reg_get fr r) ->
     aroom A1 vm1 (kR - RK_pix) (bR - RB_amb (p_w v) (p_h v) 11) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs1 (Z_to_bv 64 0x3c0f8) m1 al_rom) (with_vmmaps vm1 md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x398e4) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pixs v ret S CK HW FZ H2 Hs16 Hstk Htop H1 Hret H4 H10 H11 H12 F10 F11 SRC Hrc Hl0 Hw22 Hh22
    kR bR AR HkR HbR KERR KOK.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  cbv [ll_img LLU16 snd] in Cimg.
  pose proof SRC as (PX & _ & _ & _ & _ & _ & _ & Lp & Ld & _ & _).
  pose proof PX as (Hp0 & Hp64 & _).
  pose proof (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  pose proof HW as [WI _ _ _ _ _ _ _ _ _ _].
  pose proof (ai_live_hull _ _ _ _ _ WI Lp) as (_ & ALp & _ & _). rewrite u_Z2bv in ALp by lia.
  pose proof (bc_m16_8 _ ALp) as Hpm8.
  pose proof (exW_blk_img_apart C A m md pixs 64 CK HW Lp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [ll_img LLU16 fst snd]; lia)) as Hpi.
  cbv [ll_img LLU16 fst snd] in Hpi.
  assert (R20 : rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1)) by (rewrite <- Hrc; exact (PIX_rd_rc SEGS m pixs v PX)).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_A al_rom fr cs regs m s pixs FZ ltac:(lia) ltac:(lia) ltac:(lia) Hpm8
             (fun j Hj => W_img16 C A m md j HW ltac:(lia)) ltac:(lia) Hpi R20
             (W_sok_win C A m md (s - 320) 320 CK HW ltac:(lia) ltac:(zlia))
             (exW_sok_blk SEGS C A m md pixs 64 (pixs + 20) 4 p16_segs CK HW Lp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(zlia))
             H2 H10 H11 H12 F10 F11) |].
  intros fin (fr1 & cs1 & r1 & M1 & -> & FZ1 & RI1 & C20 & S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27
              & SF8 & SF9 & SF18 & C288 & C160 & C272 & G1 & G2 & G10 & G11 & G12 & G13 & G14 & G22 & G24 & AG1 & E8 & E9 & EK1).
  pose proof (bc_cells_A M1 s regs fr S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27 SF8 SF9 SF18 C288 C272) as CL1.
  assert (W1 : W C A M1 md).
  { apply (rinv_W C A m md M1 [((s - 320)%Z, 320%Z); ((pixs + 20)%Z, 4%Z)] s CK HW Htop RI1).
    unfold own_regions. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
    right. exists (Z_to_bv 64 pixs), 64%Z. cbn [fst snd]. rewrite u_Z2bv by lia. refine (conj Lp (conj Hl0 (conj _ _))); lia. }
  assert (PX1 : PIXat M1 pixs (set_rc v 2)).
  { eapply PIXat_rc_set; [exact PX | | | exact C20 | lia].
    - intros x Hx Hn. rinv_out RI1.
    - intros j Hj. apply (proj1 RI1). eapply PIXat_defined; [exact PX | rewrite u_Z2bv by lia; lia]. }
  assert (SRC1 : bl_src A M1 pixs (set_rc v 2)) by (destruct SRC as (_ & Rest); exact (conj PX1 Rest)).
  refine (H_amb (mkFP fr1 cs1) C A M1 md r1 (s - 320)%Z pixs 11%Z (set_rc v 2%Z) (Z_to_bv 64 0x399b0) S CK W1 G2
            (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl) ltac:(unfold AMB_STACK, LSF; lia) ltac:(lia) G1 ltac:(red; apply bv_eq; reflexivity)
            ltac:(csr; reflexivity) G10 G11 G12 G13 G14 SRC1 (or_introl eq_refl) ltac:(cbn [set_rc p_w]; lia) ltac:(cbn [set_rc p_h]; lia)
            kR bR AR HkR HbR _).
  intros A2 m2 vm2 r2 W2 CS2 PM2 OUT2 AR2.
  assert (SL2 : sub_live A A2).
  { destruct OUT2 as [[_ LV] | (pd & dd & _ & _ & PRN)]; [apply sub_live_eq; exact LV|].
    destruct PRN as (_ & _ & _ & _ & _ & _ & _ & P8 & P9 & _ & _ & P12 & P13 & P14 & _ & _).
    exact (sub_live_new2 A A2 (Z_to_bv 64 pd) (Z_to_bv 64 dd) _ _ P8 P9 P12 P13 P14). }
  assert (LA2p : live A2 (Z_to_bv 64 pixs) = Some 64%Z) by (apply SL2; exact Lp).
  assert (CL2 : cellsAt SEGS m2 (s - 320) (bc_saved regs fr ++ [(32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z)])).
  { pose proof (agree_of_FRM C (s - 320) M1 m2 (s - 320) 320 [] CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia)) as AG.
    keep_cells CL1 AG CLx. exact CLx. }
  assert (R160b : rdn SEGS m2 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { rewrite (FRM_rdn16 C (s - 320) M1 m2 (s - 160) 8 CK (proj1 PM2)) by zlia. exact C160. }
  assert (R20b : rdn SEGS m2 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (bc_rdn_keep M1 m2) by first [zlia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
                                                  apply (bc_livk_at A M1 m2 pixs 64 a (proj2 PM2) Lp); lia].
    exact C20. }
  assert (PX2 : PIXat m2 pixs (set_rc v 2)).
  { eapply PIXat_frame; [exact PX1|]. intros x Hx. apply (bc_livk_at A M1 m2 pixs 64 x (proj2 PM2) Lp); lia. }
  assert (SRC2 : bl_src A2 m2 pixs (set_rc v 2)).
  { destruct SRC as (_ & Hd & Hcm & Hhdr & Hw1 & Hh1 & Hwpl & _ & Ld' & Hxr & Hyr).
    exact (conj PX2 (conj Hd (conj Hcm (conj Hhdr (conj Hw1 (conj Hh1 (conj Hwpl (conj LA2p (conj (SL2 _ _ Ld') (conj Hxr Hyr)))))))))). }
  apply (bc_mid fr1 cs1 C A2 m2 (with_vmmaps vm2 md) r2 s pixs (u (getr r2 10)) (set_rc v 2) S CK W2 Hstk Htop Hs16
           ltac:(csr; reflexivity) ltac:(rewrite Z_to_bv_bv_unsigned; reflexivity) (bc_u64 _) R160b SRC2).
  intros m4 r4 minv maxv W4 Hmin Hmax R148 R152 AG4 FR4 G42 G48 G49 RR4.
  assert (CL4 : cellsAt SEGS m4 (s - 320) (bc_saved regs fr ++ [(32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z)])) by (keep_cells CL2 AG4 CLx; exact CLx).
  unfold agree_win in AG4.
  assert (R160d : rdn SEGS m4 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { rewrite (bc_rdn_keep m2 m4) by first [zlia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; apply AG4; [lia |
       let rr := fresh "rr" in let Hr := fresh "Hr" in intros rr Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia]].
    exact R160b. }
  assert (R20d : rdn SEGS m4 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (bc_rdn_keep m2 m4) by first [zlia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; apply FR4; lia].
    exact R20b. }
  assert (SOK352 : store_ok SEGS m4 (Z_to_bv 64 (s - 352)) 352 = true) by (apply (W_sok_win C A2 m4 _ (s - 352) 352 CK W4); zlia).
  assert (SOK20 : store_ok SEGS m4 (Z_to_bv 64 (pixs + 20)) 4 = true)
    by exact (exW_sok_blk SEGS C A2 m4 _ pixs 64 (pixs + 20) 4 p16_segs CK W4 LA2p ltac:(lia) ltac:(lia) ltac:(lia) ltac:(zlia)).
  assert (PM14 : POSTM C A s M1 m4).
  { apply (POSTM_trans C A s M1 m2 m4); [apply (POSTM_mono C A (s - 320) s M1 m2); [lia | exact PM2] |].
    apply (POSTM_sub C A A2 s m2 m4 SL2).
    apply (POSTM_range C A2 m2 _ m4 (c_top C - LSTK) s s CK W2 FR4); lia. }
  destruct OUT2 as [[N10 LVEQ] | (bsc & datasc & N10 & HH & PRN)].
  - rewrite N10, u_Z2bv in G49 by lia.
    eapply rz_reach; [exact (w_pure _ _ _ _ W4) |
      exact (bc_Dn al_rom fr1 cs1 r4 m4 s pixs FZ1 ltac:(lia) Hs16 ltac:(lia) ltac:(lia) Hpm8 R160d R20d
               (W_clr_got C A2 m4 _ W4) (W_clr_sev C A2 m4 _ W4) ltac:(lia) Hpi SOK352 SOK20 G42 G49 G48) |].
    intros fin (r5 & M5 & -> & RI5 & C20e & G51 & G52 & G510 & G511 & G512 & AG5).
    assert (W5 : W C A2 M5 (with_vmmaps vm2 md)).
    { apply (rinv_W C A2 m4 _ M5 _ s CK W4 Htop RI5). unfold own_regions.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        first [left; lia | right; exists (Z_to_bv 64 pixs), 64%Z; rewrite u_Z2bv by lia; refine (conj LA2p (conj Hl0 (conj _ _))); lia]. }
    assert (CL5 : cellsAt SEGS M5 (s - 320) (bc_saved regs fr ++ [(32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z)])).
    { assert (AG : agree_win (s - 320) 320 [(160%Z, 8%Z); (24%Z, 8%Z)] m4 M5).
      { eapply agree_of_rinv; [exact RI5|].
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [right; exists (160%Z, 8%Z); split; [cbn [In]; auto | cbn [fst snd]; lia]|].
        apply Forall_cons; [right; exists (24%Z, 8%Z); split; [cbn [In]; auto | cbn [fst snd]; lia]|].
        apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_nil. }
      keep_cells CL4 AG CLx. exact CLx. }
    replace (Z_to_bv 64 0x17ec4) with (0x17ec4 : word) by (apply bv_eq; reflexivity).
    apply (returnErrorPtr_W (fx := mkFP fr1 cs1) C A2 M5 _ r5 (s - 320) 0x12528 0x10a26 14 15 (Z_to_bv 64 0x39cc4) (Z_to_bv 64 0) S CK W5 G52
             (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl) ltac:(unfold LSF; lia) ltac:(lia) G51 ltac:(red; apply bv_eq; reflexivity)
             G510 G511 G512 str_bc_msg str_bc_proc).
    intros m6 r6 W6 FR6 GR6 CS6 V6.
    assert (CL6 : cellsAt SEGS m6 (s - 320) (bc_saved regs fr ++ [(32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z)])).
    { pose proof (agree_of_range (s - 320 - (16 + LSF)) (s - 320) M5 m6 (s - 320) 320 [] FR6 ltac:(lia)) as AG.
      keep_cells CL5 AG CLx. exact CLx. }
    unfold bc_saved in CL6. cbn [app] in CL6.
    eapply rz_reach; [exact (w_pure _ _ _ _ W6) | |].
    { apply (bc_Vn al_rom fr1 cs1 r6 m6 s ret (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
               (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
               (Z_to_bv 64 (u (reg_get fr 8))) (Z_to_bv 64 (u (reg_get fr 9))) (Z_to_bv 64 (u (reg_get fr 18))) FZ1 ltac:(lia) Hret H1).
      all: first [ (rewrite bc_w2b; cell_from CL6) | (csr; reflexivity) ]. }
    intros fin (fr6 & cs6 & r7 & M7 & -> & FZ6 & -> & P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27
                & AG7 & Q8 & Q9 & Q18 & QK).
    apply (KERR fr6 cs6 A2 m6 vm2 r7 W6 FZ6).
    + apply cs_kept_intro; csr; reflexivity.
    + apply (POSTM_trans C A s m M5 m6).
      * eapply POSTM_bracket with (segs := SEGS) (Ar := A) (A := A) (A' := A2) (mD := M1) (mh := m4) (s' := s)
          (c := (pixs + 20)%Z) (n := 4%nat) (RD := [((s - 320)%Z, 320%Z)])
          (RE := [((s - 352)%Z, 32%Z); ((s - 160)%Z, 8%Z); ((s - 296)%Z, 8%Z)])
          (bs := Z_to_le_bytes 4 1) (p := Z_to_bv 64 pixs) (np := 64%Z).
        all: first [ exact CK | exact HW | exact W4 | exact (sub_live_refl A) | exact SL2 | exact Lp | exact RI1 | exact RI5 | exact R20
                   | exact C20e | exact PM14 | reflexivity
                   | (unfold local_regions; repeat apply Forall_cons; try apply Forall_nil; left; cbn [fst snd]; lia)
                   | (rewrite ?u_Z2bv by lia; zlia) ].
      * apply (POSTM_sub C A A2 s M5 m6 SL2).
        apply (POSTM_range C A2 M5 _ m6 (s - 320 - (16 + LSF)) (s - 320) s CK W5 FR6); unfold LSF; lia.
    + csr; reflexivity.
    + exact LVEQ.
    + intros r Hr.
      destruct (bv_eq_dec _ r 8%bv) as [->|N8]; [rewrite Q8, Z_to_bv_bv_unsigned; reflexivity|].
      destruct (bv_eq_dec _ r 9%bv) as [->|N9]; [rewrite Q9, Z_to_bv_bv_unsigned; reflexivity|].
      destruct (bv_eq_dec _ r 18%bv) as [->|N18]; [rewrite Q18, Z_to_bv_bv_unsigned; reflexivity|].
      rewrite (QK r (fs_notin_V r N8 N9 N18)). apply EK1. exact (fs_notin_A r Hr N8 N9).
    + exact AR2.
  - assert (Hbr : (4096 <= bsc)%Z /\ (bsc + 64 <= alloc_top (c_vm C))%Z) by (destruct PRN as (Pb1 & Pb2 & _); split; assumption).
    assert (Lb : live A2 (Z_to_bv 64 bsc) = Some 64%Z) by (destruct PRN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P12 & _); exact P12).
    assert (Nb : live A (Z_to_bv 64 bsc) = None) by (destruct PRN as (_ & _ & _ & _ & _ & _ & _ & P8 & _); exact P8).
    rewrite N10, u_Z2bv in G49 by lia.
    eapply rz_reach; [exact (w_pure _ _ _ _ W4) |
      exact (bc_D al_rom fr1 cs1 r4 m4 s pixs bsc FZ1 ltac:(lia) Hs16 ltac:(lia) ltac:(lia) Hpm8 ltac:(lia) R160d R20d SOK352 SOK20 G42 G49) |].
    intros fin (r5 & M5 & -> & RI5 & C20e & C296 & G51 & G52 & G510 & G511 & AG5).
    assert (W5 : W C A2 M5 (with_vmmaps vm2 md)).
    { apply (rinv_W C A2 m4 _ M5 _ s CK W4 Htop RI5). unfold own_regions.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        first [left; lia | right; exists (Z_to_bv 64 pixs), 64%Z; rewrite u_Z2bv by lia; refine (conj LA2p (conj Hl0 (conj _ _))); lia]. }
    assert (CL5 : cellsAt SEGS M5 (s - 320) (bc_saved regs fr ++ [(32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z)])).
    { assert (AG : agree_win (s - 320) 320 [(160%Z, 8%Z); (24%Z, 8%Z)] m4 M5).
      { eapply agree_of_rinv; [exact RI5|].
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [right; exists (160%Z, 8%Z); split; [cbn [In]; auto | cbn [fst snd]; lia]|].
        apply Forall_cons; [right; exists (24%Z, 8%Z); split; [cbn [In]; auto | cbn [fst snd]; lia]|].
        apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_nil. }
      keep_cells CL4 AG CLx. exact CLx. }
    assert (Hbp : (bsc + 64 <= pixs \/ pixs + 64 <= bsc)%Z).
    { apply (exW_blk_apart C A2 m2 _ bsc pixs 64 64 CK W2 Lb LA2p); [intro E; subst bsc; congruence | lia | lia | lia | lia]. }
    apply (KOK fr1 cs1 A2 M5 vm2 r5 bsc datasc minv maxv W5 FZ1).
    + eapply POSTM_bracket with (segs := SEGS) (Ar := A) (A := A) (A' := A2) (mD := M1) (mh := m4) (s' := s)
        (c := (pixs + 20)%Z) (n := 4%nat) (RD := [((s - 320)%Z, 320%Z)])
        (RE := [((s - 352)%Z, 32%Z); ((s - 160)%Z, 8%Z); ((s - 296)%Z, 8%Z)])
        (bs := Z_to_le_bytes 4 1) (p := Z_to_bv 64 pixs) (np := 64%Z).
      all: first [ exact CK | exact HW | exact W4 | exact (sub_live_refl A) | exact SL2 | exact Lp | exact RI1 | exact RI5 | exact R20
                 | exact C20e | exact PM14 | reflexivity
                 | (unfold local_regions; repeat apply Forall_cons; try apply Forall_nil; left; cbn [fst snd]; lia)
                 | (rewrite ?u_Z2bv by lia; zlia) ].
    + apply bc_cells_fl1; [exact CL5 | exact C296 | |].
      * rewrite (bc_rdn_keep m4 M5) by first [zlia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; rinv_out RI5].
        exact R148.
      * rewrite (bc_rdn_keep m4 M5) by first [zlia | intros a Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; rinv_out RI5].
        exact R152.
    + exact Hmin.
    + exact Hmax.
    + exact HH.
    + apply (bc_pixr_frame C A A2 m2 M5 bsc datasc _ PRN). intros x Hx.
      transitivity (m4 x); [rinv_out RI5 | apply FR4; lia].
    + exact G51.
    + exact G52.
    + csr; reflexivity.
    + exact G510.
    + exact G511.
    + csr; reflexivity.
    + csr; reflexivity.
    + csr; reflexivity.
    + intros r CSr NIN.
      pose proof (bc_cs_rest r CSr (fun E => NIN ltac:(rewrite E; in_lit)) (fun E => NIN ltac:(rewrite E; in_lit))
                    (fun E => NIN ltac:(rewrite E; in_lit))) as Hin.
      unfold cs_rest in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [first [(csr; reflexivity) | (exfalso; apply NIN; in_lit)]|]). destruct Hin.
    + exact E8.
    + exact E9.
    + intros r Hr N8 N9. apply EK1. exact (fs_notin_A r Hr N8 N9).
    + exact AR2.
Qed.
End BilCW1.
