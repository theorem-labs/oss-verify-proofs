(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSel LeptSlots LeptExecT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptCselsSpec V23LeptCloseSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptRop O23LeptDilW O23LeptCloseSpec O23LeptCloseIface O23LeptCloseSegs O23LeptCloseA.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition pcS (sh : bool) : Z := if sh then 0xa49c4 else 0xa4a18.      (* [comment removed for export] *)
Definition pcD (sh : bool) : Z := if sh then 0xa4aec else 0xa4b34.      (* [comment removed for export] *)
Definition pcE (sh : bool) : Z := if sh then 0xa4b04 else 0xa4b4c.      (* [comment removed for export] *)
Definition pcF (sh : bool) : Z := if sh then 0xa4b1c else 0xa4bd8.      (* [comment removed for export] *)

Lemma ret_ok_pcS : forall sh, ret_ok (Z_to_bv 64 (pcS sh)).
Proof.
  intros sh. destruct sh; red; apply bv_eq; reflexivity.
Qed.
Lemma ret_ok_pcD : forall sh, ret_ok (Z_to_bv 64 (pcD sh)).
Proof.
  intros sh. destruct sh; red; apply bv_eq; reflexivity.
Qed.
Lemma ret_ok_pcE : forall sh, ret_ok (Z_to_bv 64 (pcE sh)).
Proof.
  intros sh. destruct sh; red; apply bv_eq; reflexivity.
Qed.
Lemma ret_ok_pcF : forall sh, ret_ok (Z_to_bv 64 (pcF sh)).
Proof.
  intros sh. destruct sh; red; apply bv_eq; reflexivity.
Qed.

Section SegsG.
Context {fx : FPState}.
Variable rom : word -> option byte.

Lemma ms_conv : forall regs regs' (a a' b b' : word) m m', a = a' -> b = b' ->
  msteps SEGS (mkst regs a m rom) (mkst regs' b m' rom) -> msteps SEGS (mkst regs a' m rom) (mkst regs' b' m' rom).
Proof. intros regs regs' a a' b b' m m' -> ->. exact (fun H => H). Qed.

Lemma cs_A : forall (sh : bool) regs m (s pix1 : Z) (ret : word),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1)%Z -> (pix1 + 64 < 2 ^ 64)%Z -> (pix1 mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 (pix1 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 ->
  getr regs 12 = Z_to_bv 64 (O23LeptCloseA.hsz sh) -> getr regs 13 = Z_to_bv 64 (O23LeptCloseA.vsz sh) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4878 : word) m rom) (mkst regs' (0xa3574 : word) (O23LeptCloseSegs.FRC m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 (pcS sh)
    /\ getr regs' 8 = Z_to_bv 64 pix1 /\ getr regs' 9 = Z_to_bv 64 2 /\ getr regs' 18 = Z_to_bv 64 (O23LeptCloseA.hsz sh) /\ getr regs' 19 = Z_to_bv 64 (O23LeptCloseA.vsz sh)
    /\ getr regs' 20 = Z_to_bv 64 pix1
    /\ getr regs' 10 = Z_to_bv 64 (O23LeptCloseA.ssz sh) /\ getr regs' 11 = Z_to_bv 64 (O23LeptCloseA.sdir sh) /\ getr regs' 12 = Z_to_bv 64 (O23LeptCloseA.co1 sh s) /\ getr regs' 13 = Z_to_bv 64 (O23LeptCloseA.co2 sh s)
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20]%list) regs regs'.
Proof.
  intros sh regs m s pix1 ret Hs Hs64 Hp Hp64 AL SOK R1 R2 H2 H1 H10 H11 H12 H13.
  destruct sh.
  - destruct (cs_A_h rom regs m s pix1 ret Hs Hs64 Hp Hp64 AL SOK R1 R2 H2 H1 H10 H11 H12 H13) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
  - destruct (cs_A_v rom regs m s pix1 ret Hs Hs64 Hp Hp64 AL SOK R1 R2 H2 H1 H10 H11 H12 H13) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
Qed.

Lemma cs_C : forall (sh : bool) regs m (pix1 : Z),
  getr regs 10 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 2 -> getr regs 18 = Z_to_bv 64 (O23LeptCloseA.hsz sh) -> getr regs 19 = Z_to_bv 64 (O23LeptCloseA.vsz sh) ->
  getr regs 20 = Z_to_bv 64 pix1 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 (pcS sh)) m rom) (mkst regs' (0x70e84 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4ad0 /\ getr regs' 9 = Z_to_bv 64 32 /\ getr regs' 10 = Z_to_bv 64 pix1 /\ getr regs' 11 = Z_to_bv 64 32
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12]%list) regs regs'.
Proof.
  intros sh regs m pix1 H10 H9 H18 H19 H20.
  destruct sh.
  - destruct (cs_C_h rom regs m pix1 H10 H9 H18 H19 H20) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
  - destruct (cs_C_v rom regs m pix1 H10 H9 H18 H19 H20) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
Qed.

Lemma cs_D : forall (sh : bool) regs m (s pixsb sel1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel1 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
  rdn SEGS (O23LeptCloseSegs.CW8 m (s - 56) pixsb) (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixsb -> getr regs 18 = Z_to_bv 64 (O23LeptCloseA.hsz sh) -> getr regs 19 = Z_to_bv 64 (O23LeptCloseA.vsz sh) ->
  exists regs',
    msteps SEGS (mkst regs (0xa4ad0 : word) m rom) (mkst regs' (0xa1968 : word) (O23LeptCloseSegs.CW8 m (s - 56) pixsb) rom)
    /\ getr regs' 1 = Z_to_bv 64 (pcD sh) /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixsb /\ getr regs' 12 = Z_to_bv 64 sel1
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros sh regs m s pixsb sel1 Hs Hs64 Hsel SOK R H2 H10 H18 H19.
  destruct sh.
  - destruct (cs_D_h rom regs m s pixsb sel1 Hs Hs64 Hsel SOK R H2 H10 H18 H19) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
  - destruct (cs_D_v rom regs m s pixsb sel1 Hs Hs64 Hsel SOK R H2 H10 H18 H19) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
Qed.

Lemma cs_E : forall (sh : bool) regs m (s pixt sel2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel2 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.co2 sh s)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 (pcD sh)) m rom) (mkst regs' (0xa1968 : word) (O23LeptCloseSegs.CW8 m (s - 64) pixt) rom)
    /\ getr regs' 1 = Z_to_bv 64 (pcE sh) /\ getr regs' 19 = Z_to_bv 64 pixt /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixt
    /\ getr regs' 12 = Z_to_bv 64 sel2
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 19]%list) regs regs'.
Proof.
  intros sh regs m s pixt sel2 Hs Hs64 Hsel SOK R H2 H10.
  destruct sh.
  - destruct (cs_E_h rom regs m s pixt sel2 Hs Hs64 Hsel SOK R H2 H10) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
  - destruct (cs_E_v rom regs m s pixt sel2 Hs Hs64 Hsel SOK R H2 H10) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
Qed.

Lemma cs_F : forall (sh : bool) regs m (s pixt pixdb sel1 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel1 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 pixdb -> getr regs 19 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 (pcE sh)) m rom) (mkst regs' (0xa1d7c : word) (O23LeptCloseSegs.CW8 m (s - 72) pixdb) rom)
    /\ getr regs' 1 = Z_to_bv 64 (pcF sh) /\ getr regs' 18 = Z_to_bv 64 pixdb /\ getr regs' 10 = Z_to_bv 64 pixt /\ getr regs' 11 = Z_to_bv 64 pixdb
    /\ getr regs' 12 = Z_to_bv 64 sel1
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof.
  intros sh regs m s pixt pixdb sel1 Hs Hs64 Hsel SOK R H2 H10 H19.
  destruct sh.
  - destruct (cs_F_h rom regs m s pixt pixdb sel1 Hs Hs64 Hsel SOK R H2 H10 H19) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
  - destruct (cs_F_v rom regs m s pixt pixdb sel1 Hs Hs64 Hsel SOK R H2 H10 H19) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
Qed.

Lemma cs_G : forall (sh : bool) regs m (s pixt pixdb sel2 : Z),
  (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sel2 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.co2 sh s)) 8 = Some (Z_to_le_bytes 8 sel2) ->
  getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 18 = Z_to_bv 64 pixdb -> getr regs 19 = Z_to_bv 64 pixt ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 (pcF sh)) m rom) (mkst regs' (0xa1d7c : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa4be8 /\ getr regs' 10 = Z_to_bv 64 pixdb /\ getr regs' 11 = Z_to_bv 64 pixt /\ getr regs' 12 = Z_to_bv 64 sel2
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros sh regs m s pixt pixdb sel2 Hs Hs64 Hsel R H2 H18 H19.
  destruct sh.
  - destruct (cs_G_h rom regs m s pixt pixdb sel2 Hs Hs64 Hsel R H2 H18 H19) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
  - destruct (cs_G_v rom regs m s pixt pixdb sel2 Hs Hs64 Hsel R H2 H18 H19) as (R' & MS & HH).
    exists R'; split; [eapply ms_conv; [ | | exact MS]; apply bv_eq; reflexivity | exact HH].
Qed.
End SegsG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bundles.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma LIVK_of_PWK : forall C Ar A (P : word -> Prop) m md m', Cok C -> W C A m md ->
  O23LeptCloseA.PWK A P m m' -> (forall q k, live Ar q = Some k -> live A q = Some k /\ P q) -> LIVK Ar m m'.
Proof.
  intros C Ar A P m md m' CK HW PW HS q k i Lq Hi.
  destruct (HS q k Lq) as [LA PQ].
  pose proof (ai_live_hull A m (m_vmmaps md) q k (w_inv _ _ _ _ HW) LA) as (Hk0 & _ & TOP & _).
  pose proof (u64_range q). pose proof (round16_ge k Hk0). pose proof (alloc_top_lt (m_vmmaps md)) as AT. unfold two_pow_64 in AT.
  apply (PW q k (at_ q i) LA PQ). unfold at_. rewrite u_Z2bv; lia.
Qed.

(* [comment removed for export] *)
Lemma FRM_pw : forall C x m m', Cok C -> FRM C x m m' -> (c_top C - LSTK <= x)%Z -> forall a : word, (x <= u a)%Z -> m' a = m a.
Proof.
  intros C x m m' CK F Hx a Ha. pose proof CK as [T1 T2 T3 T4 T5].
  pose proof pin_ag_img as AG. pose proof pin_errno_img as ER. pose proof pin_hcell as (HC1 & HC2 & _).
  apply F.
  - apply above_not_gap. lia.
  - intros G. pose proof (pin_glob a G) as I. unfold inZ in I. lia.
  - intros G. pose proof (pin_errno a G) as I. unfold inZ in I. lia.
  - unfold hcell. lia.
  - unfold scratch. lia.
Qed.

(* [comment removed for export] *)
Definition FRS (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)).

Lemma FRS_FRC : forall m s ret regs, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> FRS (O23LeptCloseSegs.FRC m s ret regs) s ret regs.
Proof.
  intros m s ret regs Hs Hs64. unfold FRS, O23LeptCloseSegs.FRC. repeat split; rdn_solve.
Qed.

Lemma FRS_keep : forall m m' s ret regs, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> FRS m s ret regs ->
  (forall a : word, (s - 48 <= u a < s)%Z -> m' a = m a) -> FRS m' s ret regs.
Proof.
  intros m m' s ret regs Hs Hs64 (F1 & F2 & F3 & F4 & F5 & F6) K.
  assert (KK : forall b w, (s - 48 <= b)%Z -> (b + 8 <= s)%Z -> rdn SEGS m (Z_to_bv 64 b) 8 = Some (word_to_le_bytes 8 w) ->
                  rdn SEGS m' (Z_to_bv 64 b) 8 = Some (word_to_le_bytes 8 w)).
  { intros b w Hb Hb8 R. rewrite <- R. apply rdn_ext; rewrite ?u_Z2bv by lia; [cbn; lia |]. intros x Hx. cbn in Hx. apply K. lia. }
  unfold FRS. repeat split; apply KK; try lia; assumption.
Qed.

(* [comment removed for export] *)
Lemma cell_keep : forall m m' (lo hi b v : Z), (0 <= b)%Z -> (hi <= 2 ^ 64)%Z -> (lo <= b)%Z -> (b + 8 <= hi)%Z ->
  (forall a : word, (lo <= u a < hi)%Z -> m' a = m a) ->
  rdn SEGS m (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 v) -> rdn SEGS m' (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 v).
Proof.
  intros m m' lo hi b v Hb Hhi Hlo Hb8 K R. rewrite <- R. apply rdn_ext; rewrite ?u_Z2bv by lia; [cbn; lia |].
  intros x Hx. cbn in Hx. apply K. lia.
Qed.

(* [comment removed for export] *)
Lemma CW8_rd : forall m p v, (0 <= p)%Z -> (p + 8 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS (O23LeptCloseSegs.CW8 m p v) (Z_to_bv 64 p) 8 = Some (Z_to_le_bytes 8 v).
Proof.
  intros m p0 v Hp Hp8 Hv. unfold O23LeptCloseSegs.CW8. rewrite <- (w2b_Z 8 v Hv). apply rdn_wbytes_hit8. rewrite u_Z2bv; lia.
Qed.

Lemma sel_keep : forall T A A' (P : word -> Prop) m m' sel sv c, (T < 2 ^ 64)%Z -> sel_at T A m sel sv -> sel_cont m sv c ->
  (forall q, O23LeptCloseA.sblk sel sv q -> live A' q = live A q) -> O23LeptCloseA.PWK A P m m' -> (forall q, O23LeptCloseA.sblk sel sv q -> P q) ->
  sel_at T A' m' sel sv /\ sel_cont m' sv c.
Proof.
  intros T A A' P m m' sel sv c HT SA SC LK PW PQ. split.
  - exact (O23LeptCloseA.sel_at_keepP T A A' P m m' sel sv HT SA LK PW PQ).
  - intros i j Hi Hj. destruct (SC i j Hi Hj) as [Hc R]. split; [exact Hc |]. rewrite <- R.
    destruct SA as (Hsy & Hsx & Bs & Ls & Rc & Bd & Ld & Nd & Rows & Dst). destruct (Rows i Hi) as (Br & Lr & _ & _ & _).
    unfold bok in Br. apply rdn_ext; rewrite ?u_Z2bv by lia; [cbn; lia |]. intros x Hx. cbn in Hx.
    apply (PW (Z_to_bv 64 (v_rows sv i)) (4 * v_sx sv)%Z x Lr).
    + apply PQ. exists (v_rows sv i). split; [right; right; exists i; split; [lia | reflexivity] | reflexivity].
    + rewrite u_Z2bv by lia. lia.
Qed.

Definition RST (C : lctx) (Ar : AS) (me : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (sh : bool)
    (pix1 w h cm datas : Z) (cv : cmapv) (sel1 sel2 : Z) (sv1 sv2 : selv) (c1 c2 : Z -> Z -> Z) (A : AS) (m : word -> option byte) : Prop :=
  FRS m s ret regs /\
  rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1) /\ rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.co2 sh s)) 8 = Some (Z_to_le_bytes 8 sel2) /\
  rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.cz1 sh s)) 8 = Some (Z_to_le_bytes 8 0) /\ rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.cz2 sh s)) 8 = Some (Z_to_le_bytes 8 0) /\
  sub_live Ar A /\ POSTM C Ar s me m /\
  O23LeptCloseSpec.pix1_at C Ar A m pix1 w h cm datas cv /\
  sel_at (alloc_top (c_vm C)) A m sel1 sv1 /\ sel_at (alloc_top (c_vm C)) A m sel2 sv2 /\ sel_cont m sv1 c1 /\ sel_cont m sv2 c2.

(* [comment removed for export] *)
Definition FCL (s : Z) (ret : word) (regs : bvmap 5 word) (sh : bool) (sel1 sel2 : Z) (m : word -> option byte) : Prop :=
  FRS m s ret regs /\
  rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1) /\ rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.co2 sh s)) 8 = Some (Z_to_le_bytes 8 sel2) /\
  rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.cz1 sh s)) 8 = Some (Z_to_le_bytes 8 0) /\ rdn SEGS m (Z_to_bv 64 (O23LeptCloseA.cz2 sh s)) 8 = Some (Z_to_le_bytes 8 0).

Lemma FCL_keep : forall s ret regs sh sel1 sel2 m m', (112 <= s)%Z -> (s < 2 ^ 64)%Z -> FCL s ret regs sh sel1 sel2 m ->
  (forall a : word, (s - 104 <= u a < s - 72 \/ s - 48 <= u a < s)%Z -> m' a = m a) -> FCL s ret regs sh sel1 sel2 m'.
Proof.
  intros s ret regs sh sel1 sel2 m m' Hs Hs64 (F0 & F1 & F2 & F3 & F4) K.
  assert (KK : forall b v, (s - 104 <= b)%Z -> (b + 8 <= s - 72)%Z -> rdn SEGS m (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 v) ->
                 rdn SEGS m' (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 v)).
  { intros b v Hb Hb8. apply (cell_keep m m' (s - 104) (s - 72) b v); try lia. intros a Ha. apply K. lia. }
  unfold FCL. split; [apply (FRS_keep m m' s ret regs Hs Hs64 F0); intros a Ha; apply K; lia |].
  destruct sh; unfold O23LeptCloseA.co1, O23LeptCloseA.co2, O23LeptCloseA.cz1, O23LeptCloseA.cz2 in *;
    repeat split; apply KK; try lia; assumption.
Qed.

Lemma FCL_of_RST : forall C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m,
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m -> FCL s ret regs sh sel1 sel2 m.
Proof.
  intros C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m (F0 & F1 & F2 & F3 & F4 & _).
  unfold FCL. tauto.
Qed.

Lemma RST_keep : forall C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A' (P : word -> Prop) m',
  Cok C -> (112 <= s)%Z -> (s <= c_top C)%Z ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m ->
  (forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> live A' q = live A q) ->
  O23LeptCloseA.PWK A P m m' -> (forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> P q) ->
  (forall a : word, (s - 104 <= u a < s - 72 \/ s - 48 <= u a < s)%Z -> m' a = m a) ->
  sub_live Ar A' -> POSTM C Ar s m m' ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A' m'.
Proof.
  intros C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A' P m' CK Hs Hst R LK PW PQ K SUB PM.
  pose proof CK as [T1 T2 T3 T4 T5].
  destruct R as (F0 & F1 & F2 & F3 & F4 & S0 & P0 & X1 & SA1 & SA2 & SC1 & SC2).
  assert (FC : FCL s ret regs sh sel1 sel2 m') by (apply (FCL_keep s ret regs sh sel1 sel2 m m'); [lia | lia | unfold FCL; tauto | exact K]).
  destruct FC as (G0 & G1 & G2 & G3 & G4).
  assert (ATB : (alloc_top (c_vm C) < 2 ^ 64)%Z) by (pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT; lia).
  destruct (sel_keep _ A A' P m m' sel1 sv1 c1 ATB SA1 SC1) as [SA1' SC1'].
  { intros q Hq. apply LK. unfold O23LeptCloseA.rblk. right; left; exact Hq. }
  { exact PW. }
  { intros q Hq. apply PQ. unfold O23LeptCloseA.rblk. right; left; exact Hq. }
  destruct (sel_keep _ A A' P m m' sel2 sv2 c2 ATB SA2 SC2) as [SA2' SC2'].
  { intros q Hq. apply LK. unfold O23LeptCloseA.rblk. right; right; exact Hq. }
  { exact PW. }
  { intros q Hq. apply PQ. unfold O23LeptCloseA.rblk. right; right; exact Hq. }
  assert (X1' : O23LeptCloseSpec.pix1_at C Ar A' m' pix1 w h cm datas cv).
  { apply (O23LeptCloseA.p1_keep3 C Ar A A' P m m' pix1 w h cm datas cv X1).
    - intros q Hq. apply LK. unfold O23LeptCloseA.rblk. left; exact Hq.
    - exact PW.
    - apply PQ. unfold O23LeptCloseA.rblk, O23LeptCloseA.tblk. left; left; reflexivity.
    - intros Hc. apply PQ. unfold O23LeptCloseA.rblk, O23LeptCloseA.tblk. left; right; right; split; [exact Hc | left; reflexivity]. }
  assert (PMe : POSTM C Ar s me m') by (eapply POSTM_trans; [exact P0 | exact PM]).
  exact (conj G0 (conj G1 (conj G2 (conj G3 (conj G4 (conj SUB (conj PMe (conj X1' (conj SA1' (conj SA2' (conj SC1' SC2'))))))))))).
Qed.

(* [comment removed for export] *)
Lemma RST_same : forall C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m md m' (x : Z),
  Cok C -> (112 <= s)%Z -> (s <= c_top C)%Z -> (c_top C - LSTK <= x)%Z -> (x <= s - 104)%Z -> W C A m md ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m ->
  POSTM C A x m m' ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m'.
Proof.
  intros C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m md m' x CK Hs Hst Hx1 Hx2 HW R PM.
  pose proof R as (_ & _ & _ & _ & _ & S0 & _).
  destruct PM as [FR LV].
  apply (RST_keep C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A (fun _ => True) m' CK Hs Hst R).
  - intros q _. reflexivity.
  - exact (O23LeptCloseA.PWK_livk A m m' LV).
  - intros q _. exact I.
  - intros a Ha. apply (FRM_pw C x m m' CK FR Hx1). lia.
  - exact S0.
  - apply (POSTM_sub C Ar A s m m' S0). apply (POSTM_mono C A x s m m'); [lia | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma store_livk : forall C A m md (s p v : Z), Cok C -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> W C A m md ->
  (s - 72 <= p)%Z -> (p + 8 <= s - 48)%Z -> O23LeptCloseA.PWK A (fun _ => True) m (O23LeptCloseSegs.CW8 m p v).
Proof.
  intros C A m md s p0 v CK Hlo Hhi HW Hp1 Hp2 q k x Lq _ Hx. pose proof CK as [T1 T2 T3 T4 T5].
  unfold CSC_STACK in Hlo.
  destruct (blk_byte C A m md q k x CK HW Lq Hx) as ((_ & HG) & _). pose proof (u64_range x) as UX.
  apply O23LeptCloseA.CW8_out; lia.
Qed.

(* [comment removed for export] *)
Lemma RST_store : forall C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m md (p v : Z),
  Cok C -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> W C A m md ->
  (s - 72 <= p)%Z -> (p + 8 <= s - 48)%Z ->
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m ->
  W C A (O23LeptCloseSegs.CW8 m p v) md /\ RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A (O23LeptCloseSegs.CW8 m p v).
Proof.
  intros C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m md p0 v CK Hlo Hhi HW Hp1 Hp2 R.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof R as (_ & _ & _ & _ & _ & S0 & _).
  assert (WP : W C A (O23LeptCloseSegs.CW8 m p0 v) md /\ POSTM C A s m (O23LeptCloseSegs.CW8 m p0 v))
    by (unfold O23LeptCloseSegs.CW8; apply (WP_win C A A m m md); [exact CK | split; [exact HW | apply POSTM_refl] | apply sub_live_refl
        | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia]).
  destruct WP as [HW' PM']. split; [exact HW' |].
  apply (RST_keep C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m A (fun _ => True) _ CK ltac:(lia) Hhi R).
  - intros q _. reflexivity.
  - exact (store_livk C A m md s p0 v CK ltac:(unfold CSC_STACK; lia) Hhi HW Hp1 Hp2).
  - intros q _. exact I.
  - intros a Ha. apply O23LeptCloseA.CW8_out; [lia | lia | lia].
  - exact S0.
  - exact (POSTM_sub C Ar A s m _ S0 PM').
Qed.


End Bundles.
