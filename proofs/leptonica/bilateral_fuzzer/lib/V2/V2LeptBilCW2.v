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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB LeptCellsB LeptRecs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptBl_iface V2LeptBilSegs V2LeptBilCW1 V2LeptBilCSegs2 V2LeptBilSegsK V2LeptBilSegsKF V2LeptBilSegsSR.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Section BilCW2.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition bc_bl2 (pixs bsc minv maxv nc kx kf spat rng : Z) : list cell :=
  [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z);
   (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf); (32%Z, 8%nat, spat); (40%Z, 8%nat, rng)].

(* [comment removed for export] *)
Ltac bc_asm := lazymatch goal with |- getr _ _ = _ => assumption | |- reg_get _ _ = _ => assumption | |- frm_zero _ => assumption | |- ret_ok _ => assumption | |- _ => fail end.

(* [comment removed for export] *)
Definition bc_blk (C : lctx) (A1 A : AS) (X n : Z) : Prop :=
  (4096 <= X)%Z /\ (X + n <= alloc_top (c_vm C))%Z /\ (X mod 16 = 0)%Z /\ live A (Z_to_bv 64 X) = Some n /\ live A1 (Z_to_bv 64 X) = None /\ live (c_A0 C) (Z_to_bv 64 X) = None.

Lemma kidx_ok_zero : forall (M : word -> option byte) (kx : Z), (0 <= kx)%Z -> (kx + 1024 <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < 1024)%Z -> M (at_ (Z_to_bv 64 kx) i) = Some (Z_to_bv 8 0)) -> kidx_ok kx M.
Proof.
  intros M kx H0 H1 HM v Hv. exists 0%Z. split; [|lia].
  rewrite Z_to_le_bytes_0. apply rdn_const.
  - rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
    rewrite <- (HM (u x - kx)%Z) by lia. f_equal. unfold at_. rewrite u_Z2bv by lia.
    replace (kx + (u x - kx))%Z with (u x) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.


Ltac b1_zlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Ltac b1_side := first [ solve [lia] | solve [rewrite alloc_margin_small by lia; lia] | solve [unfold ROOM_NMAX; lia]
  | solve [red; apply bv_eq; reflexivity] | solve [unfold CALLOC_STACK, ALLOC_STACK; lia]
  | solve [apply bc_msub; [lia | assumption | reflexivity]] ].

Ltac b1_cells := unfold cellsAt;
  repeat (apply Forall_cons; [cbn [c_off c_len c_val fst snd];
    first [ assumption
          | match goal with |- rdn ?sg ?mm (Z_to_bv 64 ?b) ?n = Some (Z_to_le_bytes ?n ?z) =>
              match goal with H : rdn sg mm (Z_to_bv 64 ?a) n = Some (Z_to_le_bytes n z) |- _ => replace b with a by lia; exact H end end ] |]);
  apply Forall_nil.

Ltac b1_ncs Hcs := exfalso; unfold AllocIface.callee_saved in Hcs; destruct Hcs as [E|[E|[E|[E|[E|E]]]]];
  first [ apply bv_eq in E; cbv in E; discriminate E
        | cbv in E; destruct E as [E1 E2]; first [apply E1; reflexivity | apply E2; reflexivity] ].

Lemma b1_cs_E : forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv ->
  ~ In r [1; 8; 9; 10; 11; 12]%bv.
Proof.
  intros r Hcs Hn Hin. apply Hn. cbn [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [solve [in_lit] | b1_ncs Hcs] |]). destruct Hin.
Qed.

Lemma b1_cs_F : forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv ->
  ~ In r [1; 5; 8; 9; 10; 11; 12; 14; 15; 16; 17]%bv.
Proof.
  intros r Hcs Hn Hin. apply Hn. cbn [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [solve [in_lit] | b1_ncs Hcs] |]). destruct Hin.
Qed.

Lemma b1_aroom : forall A vm (k b k' b' : Z), aroom A vm k b -> k = k' -> b = b' -> aroom A vm k' b'.
Proof. intros A vm k b k' b' H -> ->. exact H. Qed.

Lemma b1_cells_app1 : forall m (base : Z) (L : list cell) (c : cell), cellsAt SEGS m base L ->
  rdn SEGS m (Z_to_bv 64 (base + c_off c)) (c_len c) = Some (Z_to_le_bytes (c_len c) (c_val c)) -> cellsAt SEGS m base (L ++ [c]).
Proof. intros m base L c H1 H2. unfold cellsAt in *. apply Forall_app. split; [exact H1 | constructor; [exact H2 | constructor]]. Qed.

Lemma b1_postmc : forall C A1 Ak m md M' (R : list (Z * Z)) (s c n : Z), Cok C -> W C Ak m md -> sub_live A1 Ak -> rinv R m M' ->
  Forall (fun r => (c_top C - LSTK <= fst r /\ fst r + snd r <= s)%Z \/
    exists (p : word) (k : Z), live Ak p = Some k /\ (u p <= fst r)%Z /\ (fst r + snd r <= u p + k)%Z /\
      (live A1 p = None \/ (c <= fst r /\ fst r + snd r <= c + n)%Z)) R ->
  POSTMc C A1 s c n m M'.
Proof.
  intros C A1 Ak m md M' R s c n CK HW SL RI FR. rewrite Forall_forall in FR.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS. cbv [ll_img LLU16 snd] in Cimg.
  split.
  - intros a G1 G2 G3 G4 G5. apply (proj2 RI). intros r Hr Hin. unfold inreg in Hin.
    destruct (FR r Hr) as [[L1 L2] | (p & k & Lp & P1 & P2 & _)].
    + apply G5. unfold scratch. lia.
    + apply G1. exact (proj1 (blk_byte C Ak m md p k a CK HW Lp ltac:(lia))).
  - intros q k i Lq Hi Hc. apply (proj2 RI). intros r Hr Hin. unfold inreg in Hin.
    pose proof (SL q k Lq) as Lqk. pose proof (bc_u64 q) as Uq.
    destruct (blk_range C Ak m md q k CK HW Lqk ltac:(lia)) as [Q1 Q2].
    unfold at_ in Hin. rewrite u_Z2bv in Hin by lia.
    destruct (FR r Hr) as [[L1 L2] | (p & k' & Lp & P1 & P2 & [Np | [C1 C2]])].
    + lia.
    + assert (NE : u q <> u p).
      { intros E. assert (q = p) by (apply bv_eq; exact E). subst p. rewrite Lq in Np. discriminate. }
      pose proof (exW_blk_apart C Ak m md (u q) (u p) k k' CK HW) as AP.
      rewrite !zbv_self in AP. pose proof (bc_u64 p) as Up.
      destruct (AP Lqk Lp NE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); lia.
    + apply Hc. lia.
Qed.


Lemma bca_1 : forall fr cs C A1 m1 md r1 regs0 fr0 (s pixs bsc minv maxv : Z) (S : TSet) (kR bR : Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> W C A1 m1 md -> getr r1 1 = Z_to_bv 64 0x39a18 -> getr r1 2 = Z_to_bv 64 (s - 320) ->
  getr r1 4 = Z_to_bv 64 0x56270 -> getr r1 10 = Z_to_bv 64 1 -> getr r1 11 = Z_to_bv 64 104 -> getr r1 9 = Z_to_bv 64 bsc -> getr r1 22 = Z_to_bv 64 1 -> getr r1 24 = Z_to_bv 64 pixs ->
  cellsAt SEGS m1 (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv) -> (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> rdn SEGS m1 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  aroom A1 (m_vmmaps md) kR bR -> (6 <= kR)%Z -> (6 * 131072 <= bR)%Z ->
  (forall A' m' vm' r' (bil : Z),
     W C A' m' (with_vmmaps vm' md) -> sub_live A1 A' -> bc_blk C A1 A' bil 104 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil]) -> live A' q = live A1 q) -> aroom A' vm' (kR - 1) (bR - 131072) ->
     POSTMc C A1 s (pixs + 20) 4 m1 m' -> cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv) -> rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     getr r' 2 = Z_to_bv 64 (s - 320) -> getr r' 10 = Z_to_bv 64 bil -> getr r' 9 = Z_to_bv 64 bsc -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr cs) r' (Z_to_bv 64 0x39a18) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r1 (Z_to_bv 64 0x3c0f8) m1 al_rom) md) S.
Proof.
  intros fr cs C A1 m1 md r1 regs0 fr0 s pixs bsc minv maxv S kR bR CK Hs16 Hstk Htop HW H1 H2 H4 H10 H11 H9 H22 H24 CF Hp Lp R20
    AR HkR HbR K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk. cbv [ll_img LLU16 snd] in Cimg.
  pose proof (blk_range C A1 m1 md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  refine (W_calloc16_sure C A1 m1 md r1 1 104 kR bR _ (s - 320) S CK HW H10 H11 _ _ _ AR _ _ _ H1 _ H4 H2 _ _ _ _).
  all: try b1_side.
  intros A' m' vm' r' res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa ARa.
  change (1 * 104)%Z with 104%Z in L1.
  pose proof (bc_u64 res) as Hr64.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (bil := u res) in *. clearbody bil. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO. clear Eres.
  destruct (blk_range C A' m' _ (Z_to_bv 64 bil) 104 CK HWa L1 ltac:(lia)) as [Gb Gt]. rewrite u_Z2bv in Gb, Gt by lia.
  assert (SLa : sub_live A1 A') by exact (sub_live_new A1 A' (Z_to_bv 64 bil) 104 L0 L1 LEQ).
  assert (BBa : bc_blk C A1 A' bil 104) by (unfold bc_blk; exact (conj Gb (conj Gt (conj AL16 (conj L1 (conj L0 L00)))))).
  assert (LEa : forall q : word, ~ In q (map (Z_to_bv 64) [bil]) -> live A' q = live A1 q).
  { intros q Hq. apply LEQ. intros E. apply Hq. cbn [map In]. left. symmetry. exact E. }
  apply (K A' m' vm' r' bil HWa SLa BBa LEa).
  - eapply b1_aroom; [exact ARa | lia | rewrite alloc_margin_small by lia; lia].
  - apply POSTMc_of_POSTM. eapply POSTM_mono; [|exact PMa]; lia.
  - assert (AG : agree_win (s - 320) 320 [] m1 m') by (apply (agree_of_FRM C (s - 320)); [exact CK | exact (proj1 PMa) | lia | lia | lia]).
    keep_cells CF AG CLa. exact CLa.
  - rewrite (LIVK_rdn SEGS A1 m1 m' (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PMa) Lp) by (rewrite ?u_Z2bv by lia; b1_zlia). exact R20.
  - csr; reflexivity.
  - exact Hres.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros r Hcs _. exact (cs_kept_get r1 r' r CSa Hcs).
Qed.

Lemma bca_2 : forall fr cs C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil : Z) (S : TSet) (kR bR : Z),
  getr r1 4 = Z_to_bv 64 0x56270 ->
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero cs -> reg_get fr 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get fr 9 = Z_to_bv 64 0xffffffff40a00000 ->
  W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil]) -> live Ak q = live A1 q) -> aroom Ak vmk (kR - 1) (bR - 131072) ->
  (6 <= kR)%Z -> (6 * 131072 <= bR)%Z -> (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z ->
  (0 <= bsc < 2 ^ 64)%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk -> cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv) -> rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  getr rk 2 = Z_to_bv 64 (s - 320) -> getr rk 10 = Z_to_bv 64 bil -> getr rk 9 = Z_to_bv 64 bsc -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall fr' cs' A' m' vm' r' (nc : Z),
     frm_zero cs' -> reg_get fr' 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get fr' 9 = Z_to_bv 64 0xffffffff40a00000 ->
     (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r) -> W C A' m' (with_vmmaps vm' md) -> sub_live A1 A' -> bc_blk C A1 A' bil 104 ->
     bc_blk C A1 A' nc 40 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc]) -> live A' q = live A1 q) -> aroom A' vm' (kR - 2) (bR - 2 * 131072) -> bil <> nc -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil)]) -> rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z)] -> getr r' 2 = Z_to_bv 64 (s - 320) ->
     getr r' 10 = Z_to_bv 64 nc -> getr r' 9 = Z_to_bv 64 10 -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r' (Z_to_bv 64 0x39a74) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) rk (Z_to_bv 64 0x39a18) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros fr cs C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil S kR bR R14 CK Hs16 Hstk Htop FZ F8 F9 HW SL BB LE AR HkR HbR
    Hp Lp L0p Hmin Hmax Hbsc PM CF R20 G2 G10 G9 G22 G24 CSk K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk. cbv [ll_img LLU16 snd] in Cimg.
  pose proof BB as (Bb1 & Bb2 & Bb3 & Bbk & Bb1n & Bb0n).
  pose proof (SL _ _ Lp) as Lpk.
  pose proof (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW Lpk ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  pose proof HW as [WI _ _ _ _ _ _ _ _ _ _].
  pose proof (ai_live_hull _ _ _ _ _ WI Lpk) as (_ & ALp & _ & _). rewrite u_Z2bv in ALp by lia.
  assert (NEbp : bil <> pixs) by (intros ->; rewrite Lp in Bb1n; discriminate).
  pose proof (exW_blk_apart C Ak mk _ bil pixs 104 64 CK HW Bbk Lpk NEbp ltac:(lia) Hp ltac:(lia) ltac:(lia)) as APbp.
  pose proof CF as CLx. unfold bc_fl1, bc_saved in CLx. cbn [app] in CLx.
  assert (Rmin : rdn SEGS mk (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv)) by cell_from CLx.
  assert (Rmax : rdn SEGS mk (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv)) by cell_from CLx.
  assert (Rbsc : rdn SEGS mk (Z_to_bv 64 (s - 296)) 8 = Some (Z_to_le_bytes 8 bsc)) by cell_from CLx.
  assert (R10 : rdn SEGS mk (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10)) by cell_from CLx.
  clear CLx.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_E al_rom fr cs rk mk s pixs bsc bil minv maxv FZ ltac:(lia) ltac:(lia) ltac:(lia) ALp Hbsc Bb1 ltac:(lia) Bb3 ltac:(lia) Hmin Hmax
             Rmin Rmax Rbsc R10 R20
             (exW_sok_blk SEGS C Ak mk _ bil 104 bil 104 p16_segs CK HW Bbk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b1_zlia))
             (exW_sok_blk SEGS C Ak mk _ pixs 64 (pixs + 20) 4 p16_segs CK HW Lpk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b1_zlia))
             (W_sok_win C Ak mk _ (s - 304) 8 CK HW ltac:(lia) ltac:(b1_zlia))
             G2 G10 G9 G22 G24 F8 F9) |].
  intros fin (fr' & cs' & rE & ME & -> & FZE & RIE & E0 & E8 & E16 & E48 & E52 & E56 & E20 & E304 & E1 & E2 & E10 & E11 & E8r & E9r & AGE & FRE).
  assert (WE : W C Ak ME (with_vmmaps vmk md)).
  { apply (rinv_W C Ak mk _ ME _ s CK HW Htop RIE). unfold own_regions.
    constructor; [right; exists (Z_to_bv 64 bil), 104%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Bbk (conj Bb0n _)); lia |].
    constructor; [right; exists (Z_to_bv 64 pixs), 64%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Lpk (conj L0p _)); lia |].
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  assert (PME : POSTMc C A1 s (pixs + 20) 4 mk ME).
  { apply (b1_postmc C A1 Ak mk _ ME _ s (pixs + 20) 4 CK HW SL RIE).
    constructor; [right; exists (Z_to_bv 64 bil), 104%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Bbk (conj _ (conj _ (or_introl Bb1n)))); lia |].
    constructor; [right; exists (Z_to_bv 64 pixs), 64%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Lpk (conj _ (conj _ (or_intror _)))); lia |].
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  assert (AG1 : agree_win (s - 320) 320 [(16%Z, 8%Z)] mk ME).
  { eapply agree_of_rinv; [exact RIE |].
    constructor; [left; left; cbn [fst snd]; lia |].
    constructor; [left; left; cbn [fst snd]; lia |].
    constructor; [right; exists (16%Z, 8%Z); split; [left; reflexivity | cbn [fst snd]; lia] | constructor]. }
  keep_cells CF AG1 CLE.
  pose proof (b1_cells_app1 ME (s - 320) _ (16%Z, 8%nat, bil) CLE
    ltac:(cbn [c_off c_len c_val fst snd]; replace (s - 320 + 16)%Z with (s - 304)%Z by lia; exact E304)) as CLE2.
  assert (E4 : getr rE 4 = getr r1 4).
  { rewrite (AGE 4%bv) by notin_lit. apply CSk; [exact cs4 | notin_lit]. }
  rewrite R14 in E4.
  rewrite <- (with_vmmaps_vmmaps vmk md) in AR.
  refine (W_calloc16_sure C Ak ME (with_vmmaps vmk md) rE 10 4 (kR - 1) _ _ (s - 320) S CK WE E10 E11 _ _ _ AR _ _ _ E1 _ E4 E2 _ _ _ _).
  all: try b1_side.
  intros A' m' vm' r' res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa ARa.
  rewrite with_vmmaps_twice in HWa |- *.
  change (10 * 4)%Z with 40%Z in L1.
  pose proof (bc_u64 res) as Hr64.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (nc := u res) in *. clearbody nc. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO. clear Eres.
  destruct (blk_range C A' m' _ (Z_to_bv 64 nc) 40 CK HWa L1 ltac:(lia)) as [Gn Gnt]. rewrite u_Z2bv in Gn, Gnt by lia.
  assert (NEbn : bil <> nc) by (intros ->; rewrite Bbk in L0; discriminate).
  assert (Lbil : live A' (Z_to_bv 64 bil) = Some 104%Z).
  { rewrite LEQ; [exact Bbk | intros E; rewrite E in Bbk; rewrite Bbk in L0; discriminate]. }
  assert (L1n : live A1 (Z_to_bv 64 nc) = None).
  { destruct (live A1 (Z_to_bv 64 nc)) as [k|] eqn:E; [rewrite (SL _ _ E) in L0; discriminate | reflexivity]. }
  assert (SLa : sub_live A1 A') by exact (sub_live_trans A1 Ak A' SL (sub_live_new Ak A' (Z_to_bv 64 nc) 40 L0 L1 LEQ)).
  apply (K fr' cs' A' m' vm' r' nc FZE ltac:(rewrite FRE; exact F8) ltac:(rewrite FRE; exact F9) ltac:(intros r _ _ _ _; apply FRE) HWa SLa
           ltac:(unfold bc_blk; exact (conj Bb1 (conj Bb2 (conj Bb3 (conj Lbil (conj Bb1n Bb0n))))))
           ltac:(unfold bc_blk; exact (conj Gn (conj Gnt (conj AL16 (conj L1 (conj L1n L00))))))).
  - intros q Hq. cbn [map In] in Hq. rewrite LEQ by (intros E; apply Hq; right; left; symmetry; exact E).
    apply LE. cbn [map In]. intros [E|[]]. apply Hq. left. exact E.
  - eapply b1_aroom; [exact ARa | lia | rewrite alloc_margin_small by lia; lia].
  - exact NEbn.
  - apply (POSTMc_trans _ _ _ _ _ m1 mk); [exact PM |].
    apply (POSTMc_trans _ _ _ _ _ mk ME); [exact PME |].
    apply POSTMc_of_POSTM. apply (POSTM_sub C A1 Ak); [exact SL |]. eapply POSTM_mono; [|exact PMa]; lia.
  - assert (AGm : agree_win (s - 320) 320 [] ME m') by (apply (agree_of_FRM C (s - 320)); [exact CK | exact (proj1 PMa) | lia | lia | lia]).
    keep_cells CLE2 AGm CLm. exact CLm.
  - rewrite (LIVK_rdn SEGS Ak ME m' (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PMa) Lpk) by (rewrite ?u_Z2bv by lia; b1_zlia). exact E20.
  - assert (AGb : agree_win bil 104 [] ME m').
    { apply (agree_of_LIVK Ak ME m' (Z_to_bv 64 bil) 104); [exact (proj2 PMa) | exact Bbk | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia]. }
    apply (cells_keep SEGS bil 104 [] ME m'); [lia | lia | exact AGb | reflexivity | b1_cells].
  - csr; reflexivity.
  - exact Hres.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros r Hcs Hn. rewrite (cs_kept_get rE r' r CSa Hcs). rewrite (AGE r) by exact (b1_cs_E r Hcs Hn). exact (CSk r Hcs Hn).
Qed.

Lemma bca_3 : forall frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc : Z) (S : TSet) (kR bR : Z),
  getr r1 4 = Z_to_bv 64 0x56270 ->
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc]) -> live Ak q = live A1 q) -> aroom Ak vmk (kR - 2) (bR - 2 * 131072) -> (6 <= kR)%Z -> (6 * 131072 <= bR)%Z ->
  bil <> nc -> (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil)]) -> rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z)] -> getr rk 2 = Z_to_bv 64 (s - 320) ->
  getr rk 10 = Z_to_bv 64 nc -> getr rk 9 = Z_to_bv 64 10 -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall A' m' vm' r' (kx : Z),
     W C A' m' (with_vmmaps vm' md) -> sub_live A1 A' -> bc_blk C A1 A' bil 104 -> bc_blk C A1 A' nc 40 -> bc_blk C A1 A' kx 1024 ->
     (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx]) -> live A' q = live A1 q) -> aroom A' vm' (kR - 3) (bR - 3 * 131072) -> bil <> kx -> nc <> kx -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (72%Z, 8%nat, nc)]) -> rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> getr r' 2 = Z_to_bv 64 (s - 320) ->
     getr r' 10 = Z_to_bv 64 kx -> getr r' 9 = Z_to_bv 64 nc -> getr r' 8 = Z_to_bv 64 9 -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP frk csk) r' (Z_to_bv 64 0x39b14) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39a74) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc S kR bR R14 CK Hs16 Hstk Htop FZ HW SL BB BN LE AR HkR HbR
    NEbn Hp Lp Hmin Hmax PM CF R20 CB G2 G10 G9 G22 G24 CSk K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk. cbv [ll_img LLU16 snd] in Cimg.
  pose proof BB as (Bb1 & Bb2 & Bb3 & Bbk & Bb1n & Bb0n).
  pose proof BN as (Bn1 & Bn2 & Bn3 & Bnk & Bn1n & Bn0n).
  pose proof (SL _ _ Lp) as Lpk.
  pose proof (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW Lpk ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  assert (NEbp : bil <> pixs) by (intros ->; rewrite Lp in Bb1n; discriminate).
  assert (NEnp : nc <> pixs) by (intros ->; rewrite Lp in Bn1n; discriminate).
  pose proof (exW_blk_apart C Ak mk _ bil pixs 104 64 CK HW Bbk Lpk NEbp ltac:(lia) Hp ltac:(lia) ltac:(lia)) as APbp.
  pose proof (exW_blk_apart C Ak mk _ nc pixs 40 64 CK HW Bnk Lpk NEnp ltac:(lia) Hp ltac:(lia) ltac:(lia)) as APnp.
  pose proof (exW_blk_apart C Ak mk _ bil nc 104 40 CK HW Bbk Bnk NEbn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as APbn.
  pose proof CF as CLx. unfold bc_fl1, bc_saved in CLx. cbn [app] in CLx.
  assert (Rmin : rdn SEGS mk (Z_to_bv 64 (s - 148)) 4 = Some (Z_to_le_bytes 4 minv)) by cell_from CLx.
  assert (Rmax : rdn SEGS mk (Z_to_bv 64 (s - 152)) 4 = Some (Z_to_le_bytes 4 maxv)) by cell_from CLx.
  assert (R304 : rdn SEGS mk (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil)) by cell_from CLx.
  clear CLx.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_F al_rom (mkFP frk csk) rk mk s bil nc minv maxv ltac:(lia) Bb1 ltac:(lia) Bn1 ltac:(lia) Bn3 ltac:(lia) Hmin Hmax Rmin Rmax R304
             (exW_sok_blk SEGS C Ak mk _ nc 40 nc 40 p16_segs CK HW Bnk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b1_zlia))
             (exW_sok_blk SEGS C Ak mk _ bil 104 (bil + 64) 8 p16_segs CK HW Bbk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b1_zlia))
             (W_sok_win C Ak mk _ (s - 248) 8 CK HW ltac:(lia) ltac:(b1_zlia))
             G2 G10 G9 FZ) |].
  intros fin (rF & MF & -> & RIF & NCj & E64 & E248 & E1 & E2 & E10 & E11 & E8r & E9r & AGF).
  assert (WF : W C Ak MF (with_vmmaps vmk md)).
  { apply (rinv_W C Ak mk _ MF _ s CK HW Htop RIF). unfold own_regions.
    constructor; [right; exists (Z_to_bv 64 nc), 40%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Bnk (conj Bn0n _)); lia |].
    constructor; [right; exists (Z_to_bv 64 bil), 104%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Bbk (conj Bb0n _)); lia |].
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  assert (PMF : POSTMc C A1 s (pixs + 20) 4 mk MF).
  { apply (b1_postmc C A1 Ak mk _ MF _ s (pixs + 20) 4 CK HW SL RIF).
    constructor; [right; exists (Z_to_bv 64 nc), 40%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Bnk (conj _ (conj _ (or_introl Bn1n)))); lia |].
    constructor; [right; exists (Z_to_bv 64 bil), 104%Z; cbn [fst snd]; rewrite u_Z2bv by lia; refine (conj Bbk (conj _ (conj _ (or_introl Bb1n)))); lia |].
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  assert (R20F : rdn SEGS MF (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (rinv_rdn SEGS _ mk MF (pixs + 20) 4 RIF)
      by (first [b1_zlia | intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; b1_zlia |]); destruct Hr]).
    exact R20. }
  assert (E4 : getr rF 4 = getr r1 4).
  { rewrite (AGF 4%bv) by notin_lit. apply CSk; [exact cs4 | notin_lit]. }
  rewrite R14 in E4.
  rewrite <- (with_vmmaps_vmmaps vmk md) in AR.
  refine (W_calloc16_sure C Ak MF (with_vmmaps vmk md) rF 256 4 (kR - 2) _ _ (s - 320) S CK WF E10 E11 _ _ _ AR _ _ _ E1 _ E4 E2 _ _ _ _).
  all: try b1_side.
  intros A' m' vm' r' res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa ARa.
  rewrite with_vmmaps_twice in HWa |- *.
  change (256 * 4)%Z with 1024%Z in L1.
  pose proof (bc_u64 res) as Hr64.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (kx := u res) in *. clearbody kx. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO. clear Eres.
  destruct (blk_range C A' m' _ (Z_to_bv 64 kx) 1024 CK HWa L1 ltac:(lia)) as [Gk Gkt]. rewrite u_Z2bv in Gk, Gkt by lia.
  assert (NEbk : bil <> kx) by (intros ->; rewrite Bbk in L0; discriminate).
  assert (NEnk : nc <> kx) by (intros ->; rewrite Bnk in L0; discriminate).
  assert (Lbil : live A' (Z_to_bv 64 bil) = Some 104%Z).
  { rewrite LEQ; [exact Bbk | intros E; rewrite E in Bbk; rewrite Bbk in L0; discriminate]. }
  assert (Lnc : live A' (Z_to_bv 64 nc) = Some 40%Z).
  { rewrite LEQ; [exact Bnk | intros E; rewrite E in Bnk; rewrite Bnk in L0; discriminate]. }
  assert (L1k : live A1 (Z_to_bv 64 kx) = None).
  { destruct (live A1 (Z_to_bv 64 kx)) as [k|] eqn:E; [rewrite (SL _ _ E) in L0; discriminate | reflexivity]. }
  assert (SLa : sub_live A1 A') by exact (sub_live_trans A1 Ak A' SL (sub_live_new Ak A' (Z_to_bv 64 kx) 1024 L0 L1 LEQ)).
  apply (K A' m' vm' r' kx HWa SLa
           ltac:(unfold bc_blk; exact (conj Bb1 (conj Bb2 (conj Bb3 (conj Lbil (conj Bb1n Bb0n))))))
           ltac:(unfold bc_blk; exact (conj Bn1 (conj Bn2 (conj Bn3 (conj Lnc (conj Bn1n Bn0n))))))
           ltac:(unfold bc_blk; exact (conj Gk (conj Gkt (conj AL16 (conj L1 (conj L1k L00))))))).
  - intros q Hq. cbn [map In] in Hq. rewrite LEQ by (intros E; apply Hq; right; right; left; symmetry; exact E).
    apply LE. cbn [map In]. intros [E|[E|[]]]; apply Hq; [left | right; left]; exact E.
  - eapply b1_aroom; [exact ARa | lia | rewrite alloc_margin_small by lia; lia].
  - exact NEbk.
  - exact NEnk.
  - apply (POSTMc_trans _ _ _ _ _ m1 mk); [exact PM |].
    apply (POSTMc_trans _ _ _ _ _ mk MF); [exact PMF |].
    apply POSTMc_of_POSTM. apply (POSTM_sub C A1 Ak); [exact SL |]. eapply POSTM_mono; [|exact PMa]; lia.
  - assert (AGF1 : agree_win (s - 320) 320 [(72%Z, 8%Z)] mk MF).
    { eapply agree_of_rinv; [exact RIF |].
      constructor; [left; left; cbn [fst snd]; lia |].
      constructor; [left; left; cbn [fst snd]; lia |].
      constructor; [right; exists (72%Z, 8%Z); split; [left; reflexivity | cbn [fst snd]; lia] | constructor]. }
    keep_cells CF AGF1 CLF.
    pose proof (b1_cells_app1 MF (s - 320) _ (72%Z, 8%nat, nc) CLF
      ltac:(cbn [c_off c_len c_val fst snd]; replace (s - 320 + 72)%Z with (s - 248)%Z by lia; exact E248)) as CLF2.
    assert (AGm : agree_win (s - 320) 320 [] MF m') by (apply (agree_of_FRM C (s - 320)); [exact CK | exact (proj1 PMa) | lia | lia | lia]).
    keep_cells CLF2 AGm CLm. rewrite <- app_assoc in CLm. exact CLm.
  - rewrite (LIVK_rdn SEGS Ak MF m' (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PMa) Lpk) by (rewrite ?u_Z2bv by lia; b1_zlia). exact R20F.
  - assert (AGb : agree_win bil 104 [(64%Z, 8%Z)] mk MF).
    { eapply agree_of_rinv; [exact RIF |].
      constructor; [left; cbn [fst snd]; lia |].
      constructor; [right; exists (64%Z, 8%Z); split; [left; reflexivity | cbn [fst snd]; lia] |].
      constructor; [left; cbn [fst snd]; lia | constructor]. }
    keep_cells CB AGb CBF.
    pose proof (b1_cells_app1 MF bil _ (64%Z, 8%nat, nc) CBF ltac:(cbn [c_off c_len c_val fst snd]; exact E64)) as CBF2.
    assert (AGbm : agree_win bil 104 [] MF m').
    { apply (agree_of_LIVK Ak MF m' (Z_to_bv 64 bil) 104); [exact (proj2 PMa) | exact Bbk | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia]. }
    keep_cells CBF2 AGbm CBm. exact CBm.
  - intros j Hj. rewrite (LIVK_rdn SEGS Ak MF m' (Z_to_bv 64 nc) 40 (nc + 4 * j) 4 (proj2 PMa) Bnk) by (rewrite ?u_Z2bv by lia; b1_zlia).
    exact (NCj j Hj).
  - apply kidx_ok_zero; [lia | lia | intros i Hi; apply ZERO; lia].
  - csr; reflexivity.
  - exact Hres.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros r Hcs Hn. rewrite (cs_kept_get rF r' r CSa Hcs). rewrite (AGF r) by exact (b1_cs_F r Hcs Hn). exact (CSk r Hcs Hn).
Qed.

Ltac b4_zlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac b4_dis := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]); destruct Hr.
Ltac b4_rx := let H := fresh "H" in intro H; vm_compute in H; lia.

Lemma b4_fs2 : forall r : reg, In (u r) fs_list -> ~ In (ridx r) [14; 15]%nat.
Proof. intros r Hr Hin. unfold fs_list in Hr. unfold ridx in Hin. cbn [In] in Hr, Hin. lia. Qed.

Lemma b4_fs4 : forall r : reg, In (u r) fs_list -> ~ In (ridx r) [12; 13; 14; 15]%nat.
Proof. intros r Hr Hin. unfold fs_list in Hr. unfold ridx in Hin. cbn [In] in Hr, Hin. lia. Qed.

Lemma b4_cs3 : forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> In r [3; 4; 27]%bv.
Proof.
  intros r Hcs Hn.
  assert (N2 : r <> 2%bv) by (intros ->; apply Hn; cbn [In]; auto).
  assert (N8 : r <> 8%bv) by (intros ->; apply Hn; cbn [In]; auto).
  assert (N9 : r <> 9%bv) by (intros ->; apply Hn; cbn [In]; auto).
  pose proof (bc_cs_rest r Hcs N2 N8 N9) as H. unfold cs_rest in H. cbn [In] in H.
  destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
    first [ solve [cbn [In]; auto] | solve [exfalso; apply Hn; cbn [In]; auto 20] ].
Qed.

Lemma b4_cells_ins : forall (m : word -> option byte) (b : Z) (L : list cell) (c1 c2 c3 : cell),
  cellsAt SEGS m b (L ++ [c1; c3]) -> rdn SEGS m (Z_to_bv 64 (b + c_off c2)) (c_len c2) = Some (Z_to_le_bytes (c_len c2) (c_val c2)) ->
  cellsAt SEGS m b (L ++ [c1; c2; c3]).
Proof.
  unfold cellsAt. intros m b L c1 c2 c3 H R. apply Forall_app in H as [H1 H2].
  apply Forall_cons_iff in H2 as [Q1 H3]. apply Forall_cons_iff in H3 as [Q3 _].
  apply Forall_app. split; [exact H1|].
  apply Forall_cons; [exact Q1|]. apply Forall_cons; [exact R|]. apply Forall_cons; [exact Q3|apply Forall_nil].
Qed.

Lemma b4_kidx_rinv : forall (R : list (Z * Z)) (kx : Z) (M M' : word -> option byte), rinv R M M' -> (0 <= kx)%Z -> (kx + 1024 <= 2 ^ 64)%Z ->
  (forall r, In r R -> (kx + 1024 <= fst r \/ fst r + snd r <= kx)%Z) -> kidx_ok kx M -> kidx_ok kx M'.
Proof.
  intros R kx M M' RI H0 H1 HD KO v Hv. destruct (KO v Hv) as (kv & Hr & Hk). exists kv. split; [|exact Hk].
  rewrite (rinv_rdn SEGS R M M' (kx + 4 * v) 4 RI); [exact Hr | lia | b4_zlia |].
  intros r Hr'. specialize (HD r Hr'). b4_zlia.
Qed.

Lemma bca_4 : forall fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx : Z) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> reg_get frk 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get frk 9 = Z_to_bv 64 0xffffffff40a00000 ->
  (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get frk r = reg_get fr r) -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> bil <> nc -> bil <> kx -> nc <> kx -> (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= minv <= 255)%Z ->
  (0 <= maxv <= 255)%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk -> cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> getr rk 2 = Z_to_bv 64 (s - 320) ->
  getr rk 10 = Z_to_bv 64 kx -> getr rk 9 = Z_to_bv 64 nc -> getr rk 8 = Z_to_bv 64 9 -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall fr' cs' m' r',
     frm_zero cs' -> reg_get fr' 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get fr' 9 = Z_to_bv 64 0xffffffff40a00000 ->
     (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r) -> W C Ak m' (with_vmmaps vmk md) -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> getr r' 2 = Z_to_bv 64 (s - 320) ->
     getr r' 10 = Z_to_bv 64 kx -> getr r' 16 = Z_to_bv 64 maxv -> getr r' 8 = Z_to_bv 64 9 -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r' (Z_to_bv 64 0x39bd4) m' al_rom) (with_vmmaps vmk md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39b14) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx S CK Hs16 Hstk Htop FZ F8 F9 FK HW HSL
    Bb Bn Bk Nbn Nbk Nnk Hp Lp Hmin Hmax PM CS R20 CB NCV KO G2 G10 G9 G8 G22 G24 GK K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  destruct Bb as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6).
  destruct Bn as (Bn1 & Bn2 & Bn3 & Bn4 & Bn5 & Bn6).
  destruct Bk as (Bk1 & Bk2 & Bk3 & Bk4 & Bk5 & Bk6).
  assert (Lpk : live Ak (Z_to_bv 64 pixs) = Some 64%Z) by (apply HSL; exact Lp).
  pose proof (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW Lpk ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  assert (Dpk : (pixs + 64 <= kx \/ kx + 1024 <= pixs)%Z).
  { apply (exW_blk_apart C Ak mk _ pixs kx 64 1024 CK HW Lpk Bk4); [intro E; rewrite E in Lp; congruence | lia | lia | lia | lia]. }
  assert (Dbk : (bil + 104 <= kx \/ kx + 1024 <= bil)%Z).
  { apply (exW_blk_apart C Ak mk _ bil kx 104 1024 CK HW Bb4 Bk4); [exact Nbk | lia | lia | lia | lia]. }
  assert (Dnk : (kx + 1024 <= nc \/ nc + 40 <= kx)%Z).
  { pose proof (exW_blk_apart C Ak mk _ nc kx 40 1024 CK HW Bn4 Bk4 Nnk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as D. lia. }
  assert (SOKk : store_ok SEGS mk (Z_to_bv 64 kx) 1024 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ kx 1024 kx 1024 p16_segs CK HW Bk4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b4_zlia)).
  assert (SOK256 : store_ok SEGS mk (Z_to_bv 64 (s - 256)) 8 = true) by (apply (W_sok_win C Ak mk _ (s - 256) 8 CK HW); b4_zlia).
  pose proof CS as CS1. unfold bc_fl1, bc_saved in CS1. cbn [app] in CS1.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (kidx_seg al_rom frk csk rk mk s nc kx minv maxv FZ ltac:(lia) Bn1 ltac:(lia) Bk1 ltac:(lia) Bk3 Dnk Hmin Hmax
             ltac:(cell_from CS1) ltac:(cell_from CS1) ltac:(cell_from CS1) NCV SOKk SOK256 KO G2 G10 G9 G8) |].
  intros fin (fr' & cs' & r' & M' & -> & FZ' & RI & KO' & R256 & H2' & H10' & H16' & H8' & H9' & AG & FK').
  assert (LR : local_regions C Ak A1 s [(kx, 1024%Z); ((s - 256)%Z, 8%Z)]).
  { unfold local_regions.
    apply Forall_cons; [right; exists (Z_to_bv 64 kx), 1024%Z; rewrite u_Z2bv by lia; cbn [fst snd]; refine (conj Bk4 (conj Bk5 (conj Bk6 _))); lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_nil. }
  destruct (rinv_WP2 C A1 Ak mk (with_vmmaps vmk md) M' _ s CK HW HSL Htop RI LR) as (W' & PM').
  apply (K fr' cs' M' r' FZ').
  - rewrite FK' by b4_rx. exact F8.
  - rewrite FK' by b4_rx. exact F9.
  - intros r Hr N8 N9 N18. rewrite (FK' r (b4_fs2 r Hr)). exact (FK r Hr N8 N9 N18).
  - exact W'.
  - exact (POSTMc_trans C A1 s (pixs + 20) 4 m1 mk M' PM (POSTMc_of_POSTM C A1 s (pixs + 20) 4 mk M' PM')).
  - assert (AG1 : agree_win (s - 320) 320 [(64%Z, 8%Z)] mk M').
    { eapply agree_of_rinv; [exact RI|].
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; exists (64%Z, 8%Z); split; [cbn [In]; auto | cbn [fst snd]; lia]|]. apply Forall_nil. }
    keep_cells CS AG1 CSx. apply b4_cells_ins; [exact CSx|]. cbn [c_off c_len c_val fst snd].
    replace (s - 320 + 64)%Z with (s - 256)%Z by lia. exact R256.
  - rewrite (rinv_rdn SEGS _ mk M' (pixs + 20) 4 RI) by first [lia | b4_zlia | b4_dis]. exact R20.
  - assert (AGb : agree_win bil 104 [] mk M').
    { eapply agree_of_rinv; [exact RI|].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_nil. }
    keep_cells CB AGb CBx. exact CBx.
  - intros j Hj. rewrite (rinv_rdn SEGS _ mk M' (nc + 4 * j) 4 RI) by first [lia | b4_zlia | b4_dis]. exact (NCV j Hj).
  - exact KO'.
  - exact H2'.
  - exact H10'.
  - exact H16'.
  - exact H8'.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros r Hcs Hn. rewrite <- (GK r Hcs Hn). pose proof (b4_cs3 r Hcs Hn) as H3. cbn [In] in H3.
    destruct H3 as [<-|[<-|[<-|[]]]]; csr; reflexivity.
Qed.

Local Ltac b2_zlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Definition b2_ap (p n q k : Z) : Prop := (p + n <= q \/ q + k <= p)%Z.
Local Ltac b2_clr := repeat match goal with H : ~ @eq Z _ _ |- _ => clear H end.
Local Ltac b2_alia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
  first [ lia | match goal with H : b2_ap _ _ _ _ |- _ => let H' := fresh in pose proof H as H'; unfold b2_ap in H'; lia end ].
Local Ltac b2_rside := first [ b2_zlia | (intros ? Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; b2_alia) ].
Local Ltac b2_lside := rewrite ?u_Z2bv by lia; b2_zlia.
Local Ltac b2_room AR := rewrite LeptRoomBL.small_margin in AR by lia;
  lazymatch type of AR with aroom ?A ?v ?k ?b =>
    lazymatch goal with |- aroom _ _ ?k' ?b' => replace k' with k by lia; replace b' with b by lia; exact AR end end.

Lemma b2_kfr_ok_zero : forall (M : word -> option byte) (kf : Z), (0 <= kf)%Z -> (kf + 1024 <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < 1024)%Z -> M (at_ (Z_to_bv 64 kf) i) = Some (Z_to_bv 8 0)) -> kfr_ok kf M.
Proof.
  intros M kf H0 H1 HM v Hv. exists 0%Z. split; [|exact FpSiteB.kfr_le1_zero].
  rewrite Z_to_le_bytes_0. apply rdn_const.
  - rewrite u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
    rewrite <- (HM (u x - kf)%Z) by lia. f_equal. unfold at_. rewrite u_Z2bv by lia.
    replace (kf + (u x - kf))%Z with (u x) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma b2_cs_lo : forall r : reg, AllocIface.callee_saved r -> ~ In r [1; 10; 11; 12; 13; 14]%bv.
Proof.
  intros r CSr. destruct (cs_cases r CSr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]; notin_lit.
Qed.

Lemma b2_blk_keep : forall C A1 A A' (X n : Z) (q0 : word), bc_blk C A1 A X n -> live A q0 = None ->
  (forall q, q <> q0 -> live A' q = live A q) -> bc_blk C A1 A' X n.
Proof.
  intros C A1 A A' X n q0 (B1 & B2 & B3 & B4 & B5 & B6) N EQ.
  refine (conj B1 (conj B2 (conj B3 (conj _ (conj B5 B6))))).
  rewrite EQ; [exact B4 | intros E; rewrite E in B4; congruence].
Qed.

Lemma b2_blk_new : forall C A1 A A' m md (X n : Z), Cok C -> W C A' m md -> sub_live A1 A ->
  live A (Z_to_bv 64 X) = None -> live A' (Z_to_bv 64 X) = Some n -> live (c_A0 C) (Z_to_bv 64 X) = None ->
  (X mod 16 = 0)%Z -> (0 <= X < 2 ^ 64)%Z -> (0 < n)%Z -> bc_blk C A1 A' X n.
Proof.
  intros C A1 A A' m md X n CK HW SL N0 L1 L00 Hal HX Hn.
  destruct (blk_range C A' m md (Z_to_bv 64 X) n CK HW L1 Hn) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  refine (conj G1 (conj G2 (conj Hal (conj L1 (conj _ L00))))).
  destruct (live A1 (Z_to_bv 64 X)) eqn:E; [|reflexivity]. rewrite (SL _ _ E) in N0. discriminate.
Qed.

Lemma bca_5 : forall frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx : Z) (S : TSet) (kR bR : Z),
  getr r1 4 = Z_to_bv 64 0x56270 ->
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx]) -> live Ak q = live A1 q) -> aroom Ak vmk (kR - 3) (bR - 3 * 131072) -> (6 <= kR)%Z ->
  (6 * 131072 <= bR)%Z -> bil <> nc -> bil <> kx -> nc <> kx -> (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= maxv <= 255)%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> getr rk 2 = Z_to_bv 64 (s - 320) ->
  getr rk 10 = Z_to_bv 64 kx -> getr rk 16 = Z_to_bv 64 maxv -> getr rk 8 = Z_to_bv 64 9 -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall A' m' vm' r' (kf : Z),
     W C A' m' (with_vmmaps vm' md) -> sub_live A1 A' -> bc_blk C A1 A' bil 104 -> bc_blk C A1 A' nc 40 -> bc_blk C A1 A' kx 1024 -> bc_blk C A1 A' kf 1024 ->
     (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf]) -> live A' q = live A1 q) -> aroom A' vm' (kR - 4) (bR - 4 * 131072) -> bil <> kf -> nc <> kf -> kx <> kf ->
     POSTMc C A1 s (pixs + 20) 4 m1 m' -> cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> kfr_ok kf m' -> getr r' 2 = Z_to_bv 64 (s - 320) ->
     getr r' 10 = Z_to_bv 64 kf -> getr r' 8 = Z_to_bv 64 9 -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP frk csk) r' (Z_to_bv 64 0x39c28) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39bd4) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx S kR bR
    H4 CK Hs16 Hstk Htop FZ HW SL Bb Bn Bk LQ AR HkR HbR Nbn Nbk Nnk Hp Lp Hmax PM CF R20 CB CN KI G2 G10 G16 G8 G22 G24 GK K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  pose proof Bb as (Gb1 & Gb2 & Gb3 & Lb & Nb & N0b).
  pose proof Bn as (Gn1 & Gn2 & Gn3 & Ln & Nn & N0n).
  pose proof Bk as (Gk1 & Gk2 & Gk3 & Lk & Nk & N0k).
  pose proof (SL _ _ Lp) as Lpk.
  destruct (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW Lpk ltac:(lia)) as [Gp1 Gp2]. rewrite u_Z2bv in Gp1, Gp2 by lia.
  assert (Abk : b2_ap bil 104 kx 1024) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ bil kx 104 1024 CK HW Lb Lk Nbk); b2_clr; lia).
  assert (Abn : b2_ap bil 104 nc 40) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ bil nc 104 40 CK HW Lb Ln Nbn); b2_clr; lia).
  assert (Ank : b2_ap nc 40 kx 1024) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ nc kx 40 1024 CK HW Ln Lk Nnk); b2_clr; lia).
  assert (Apb : b2_ap pixs 64 bil 104)
    by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ pixs bil 64 104 CK HW Lpk Lb); [intro E; rewrite E in Lp; congruence | b2_clr; lia ..]).
  assert (Apk : b2_ap pixs 64 kx 1024)
    by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ pixs kx 64 1024 CK HW Lpk Lk); [intro E; rewrite E in Lp; congruence | b2_clr; lia ..]).
  b2_clr.
  pose proof CF as CF'. unfold bc_fl1, bc_saved in CF'. cbn [app] in CF'.
  assert (C288 : rdn SEGS mk (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10)) by cell_from CF'.
  assert (C304 : rdn SEGS mk (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil)) by cell_from CF'.
  clear CF'.
  assert (SOKk : store_ok SEGS mk (Z_to_bv 64 kx) 1024 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ kx 1024 kx 1024 p16_segs CK HW Lk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b2_zlia)).
  assert (SOKb : store_ok SEGS mk (Z_to_bv 64 (bil + 72)) 8 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ bil 104 (bil + 72) 8 p16_segs CK HW Lb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b2_zlia)).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_G2 al_rom (mkFP frk csk) rk mk s bil kx maxv ltac:(lia) Gb1 ltac:(lia) Gk1 ltac:(lia) Gk3 Abk Hmax C288 C304 SOKk SOKb G2 G10 G16 FZ) |].
  intros fin (r2 & M2 & -> & RI & RK8 & RB72 & Q1 & Q2 & Q10 & Q11 & AG).
  assert (WP2 : W C Ak M2 (with_vmmaps vmk md) /\ POSTM C A1 s mk M2).
  { apply (rinv_WP2 C A1 Ak mk _ M2 _ s CK HW SL Htop RI).
    unfold local_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; right; cbn [fst snd].
    - exists (Z_to_bv 64 kx), 1024%Z. rewrite u_Z2bv by lia. refine (conj Lk (conj Nk (conj N0k _))); lia.
    - exists (Z_to_bv 64 bil), 104%Z. rewrite u_Z2bv by lia. refine (conj Lb (conj Nb (conj N0b _))); lia. }
  destruct WP2 as [HW2 PM2].
  assert (AGf : agree_win (s - 320) 320 [] mk M2).
  { eapply agree_of_rinv; [exact RI|]. repeat apply Forall_cons; try apply Forall_nil; left; cbn [fst snd]; lia. }
  keep_cells CF AGf CF2.
  assert (AGb : agree_win bil 104 [(72%Z, 8%Z)] mk M2).
  { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [left; cbn [fst snd]; b2_alia|].
    apply Forall_cons; [right; exists (72%Z, 8%Z); split; [cbn [In]; auto | cbn [fst snd]; lia]|]. apply Forall_nil. }
  keep_cells CB AGb CB2.
  pose proof (cellsAt_app SEGS M2 bil _ [(72%Z, 8%nat, kx)] CB2
                (cellsAt_cons SEGS M2 bil [] 72 8 kx (bil + 72) eq_refl RB72 (cellsAt_nil SEGS M2 bil))) as CB2'.
  clear CB2.
  assert (R20b : rdn SEGS M2 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (rinv_rdn SEGS _ mk M2 (pixs + 20) 4 RI) by b2_rside. exact R20. }
  assert (CN2 : forall j, (0 <= j < 10)%Z -> rdn SEGS M2 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { intros j Hj. rewrite (rinv_rdn SEGS _ mk M2 (nc + 4 * j) 4 RI) by b2_rside. exact (CN j Hj). }
  assert (KI2 : kidx_ok kx M2).
  { intros v Hv. destruct (Z.eq_dec v maxv) as [->|Nv].
    - exists 8%Z. split; [exact RK8 | lia].
    - destruct (KI v Hv) as (kv & Rv & Hkv). exists kv. split; [|exact Hkv].
      rewrite (rinv_rdn SEGS _ mk M2 (kx + 4 * v) 4 RI) by b2_rside. exact Rv. }
  assert (Q4 : getr r2 4 = getr r1 4).
  { rewrite (AG 4%bv) by notin_lit. exact (GK 4%bv cs4 ltac:(notin_lit)). }
  rewrite H4 in Q4.
  assert (Hs16b : ((s - 320) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (RO : ret_ok (getr r2 1)) by (rewrite Q1; red; apply bv_eq; reflexivity).
  pose proof (LeptRoomBL.small_margin (256 * 4) ltac:(lia)) as SM.
  apply (W_calloc16_sure C Ak M2 _ r2 256 4 _ _ (getr r2 1) (s - 320) S CK HW2 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           AR ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) eq_refl
           RO Q4 Q2 Hs16b
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A3 m3 vm3 r3 res HW3 Hres CS3 Hnz L0 L1 L00 LEQ ZERO AL16 TOP PM3 AR3.
  rewrite ?with_vmmaps_twice in HW3 |- *.
  rewrite Q1.
  change (256 * 4)%Z with 1024%Z in *.
  pose proof (bc_u64 res) as Ures.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (kf := u res) in *. clearbody kf. clear Hnz. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO. clear Eres.
  destruct (blk_range C A3 m3 _ _ _ CK HW3 L1 ltac:(lia)) as [Gfa Gfb]. rewrite u_Z2bv in Gfa, Gfb by lia.
  assert (AGf3 : agree_win (s - 320) 320 [] M2 m3)
    by exact (agree_of_FRM C (s - 320) M2 m3 (s - 320) 320 [] CK (proj1 PM3) ltac:(lia) ltac:(lia) ltac:(lia)).
  keep_cells CF2 AGf3 CF3.
  assert (AGb3 : agree_win bil 104 [] M2 m3)
    by exact (agree_of_LIVK Ak M2 m3 (Z_to_bv 64 bil) 104 bil 104 [] (proj2 PM3) Lb ltac:(b2_lside) ltac:(b2_lside)).
  keep_cells CB2' AGb3 CB3.
  assert (R20c : rdn SEGS m3 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (LIVK_rdn SEGS Ak M2 m3 (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PM3) Lpk) by b2_lside. exact R20b. }
  assert (CN3 : forall j, (0 <= j < 10)%Z -> rdn SEGS m3 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { intros j Hj. rewrite (LIVK_rdn SEGS Ak M2 m3 (Z_to_bv 64 nc) 40 (nc + 4 * j) 4 (proj2 PM3) Ln) by b2_lside. exact (CN2 j Hj). }
  assert (KI3 : kidx_ok kx m3).
  { intros v Hv. destruct (KI2 v Hv) as (kv & Rv & Hkv). exists kv. split; [|exact Hkv].
    rewrite (LIVK_rdn SEGS Ak M2 m3 (Z_to_bv 64 kx) 1024 (kx + 4 * v) 4 (proj2 PM3) Lk) by b2_lside. exact Rv. }
  assert (KF3 : kfr_ok kf m3) by (apply b2_kfr_ok_zero; [lia | lia | exact ZERO]).
  assert (PM4 : POSTMc C A1 s (pixs + 20) 4 m1 m3).
  { apply (POSTMc_trans C A1 s (pixs + 20) 4 m1 mk m3 PM).
    apply (POSTMc_trans C A1 s (pixs + 20) 4 mk M2 m3).
    - apply POSTMc_of_POSTM. exact PM2.
    - apply POSTMc_of_POSTM. apply (POSTM_sub C A1 Ak s M2 m3 SL).
      apply (POSTM_mono C Ak (s - 320) s M2 m3); [lia | exact PM3]. }
  assert (LQ3 : forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf]) -> live A3 q = live A1 q).
  { intros q Hq. rewrite LEQ by (intro E; apply Hq; subst q; cbn [map In]; tauto).
    apply LQ. intro Hin; apply Hq; cbn [map In] in Hin |- *; tauto. }
  apply (K A3 m3 vm3 r3 kf HW3 (sub_live_trans A1 Ak A3 SL (sub_live_new Ak A3 _ _ L0 L1 LEQ))
           (b2_blk_keep C A1 Ak A3 bil 104 _ Bb L0 LEQ) (b2_blk_keep C A1 Ak A3 nc 40 _ Bn L0 LEQ)
           (b2_blk_keep C A1 Ak A3 kx 1024 _ Bk L0 LEQ)
           (b2_blk_new C A1 Ak A3 m3 _ kf 1024 CK HW3 SL L0 L1 L00 AL16 ltac:(lia) ltac:(lia)) LQ3).
  - b2_room AR3.
  - intro E; rewrite E in Lb; congruence.
  - intro E; rewrite E in Ln; congruence.
  - intro E; rewrite E in Lk; congruence.
  - exact PM4.
  - exact CF3.
  - exact R20c.
  - exact CB3.
  - exact CN3.
  - exact KI3.
  - exact KF3.
  - csr; reflexivity.
  - exact Hres.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros r CSr NIN. rewrite (cs_kept_get r2 r3 r CS3 CSr).
    rewrite (AG r) by (let H := fresh in intro H; apply (b2_cs_lo r CSr); cbn [In] in H |- *; tauto).
    exact (GK r CSr NIN).
Qed.

Lemma bca_6 : forall fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx kf : Z) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> reg_get frk 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get frk 9 = Z_to_bv 64 0xffffffff40a00000 ->
  (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get frk r = reg_get fr r) -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> bc_blk C A1 Ak kf 1024 -> bil <> nc -> bil <> kx -> nc <> kx -> bil <> kf -> nc <> kf -> kx <> kf -> (0 <= pixs < 2 ^ 64)%Z ->
  live A1 (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> kfr_ok kf mk -> getr rk 2 = Z_to_bv 64 (s - 320) ->
  getr rk 10 = Z_to_bv 64 kf -> getr rk 8 = Z_to_bv 64 9 -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall fr' cs' m' r',
     frm_zero cs' -> reg_get fr' 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get fr' 9 = Z_to_bv 64 0xffffffff40a00000 ->
     (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r) -> W C Ak m' (with_vmmaps vmk md) -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> kfr_ok kf m' -> getr r' 2 = Z_to_bv 64 (s - 320) ->
     getr r' 10 = Z_to_bv 64 kf -> getr r' 11 = Z_to_bv 64 maxv -> getr r' 28 = Z_to_bv 64 11 -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r' (Z_to_bv 64 0x39d98) m' al_rom) (with_vmmaps vmk md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39c28) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx kf S CK Hs16 Hstk Htop FZ F8 F9 FK HW HSL
    Bb Bn Bk Bf Nbn Nbk Nnk Nbf Nnf Nkf Hp Lp Hmin Hmax PM CS R20 CB NCV KO KFO G2 G10 G8 G22 G24 GK K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  destruct Bb as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6).
  destruct Bn as (Bn1 & Bn2 & Bn3 & Bn4 & Bn5 & Bn6).
  destruct Bk as (Bk1 & Bk2 & Bk3 & Bk4 & Bk5 & Bk6).
  destruct Bf as (Bf1 & Bf2 & Bf3 & Bf4 & Bf5 & Bf6).
  assert (Lpk : live Ak (Z_to_bv 64 pixs) = Some 64%Z) by (apply HSL; exact Lp).
  pose proof (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW Lpk ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  assert (Dpf : (pixs + 64 <= kf \/ kf + 1024 <= pixs)%Z).
  { apply (exW_blk_apart C Ak mk _ pixs kf 64 1024 CK HW Lpk Bf4); [intro E; rewrite E in Lp; congruence | lia | lia | lia | lia]. }
  assert (Dbf : (bil + 104 <= kf \/ kf + 1024 <= bil)%Z).
  { apply (exW_blk_apart C Ak mk _ bil kf 104 1024 CK HW Bb4 Bf4); [exact Nbf | lia | lia | lia | lia]. }
  assert (Dnf : (kf + 1024 <= nc \/ nc + 40 <= kf)%Z).
  { pose proof (exW_blk_apart C Ak mk _ nc kf 40 1024 CK HW Bn4 Bf4 Nnf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as D. lia. }
  assert (Dkf : (kx + 1024 <= kf \/ kf + 1024 <= kx)%Z).
  { apply (exW_blk_apart C Ak mk _ kx kf 1024 1024 CK HW Bk4 Bf4); [exact Nkf | lia | lia | lia | lia]. }
  assert (SOKf : store_ok SEGS mk (Z_to_bv 64 kf) 1024 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ kf 1024 kf 1024 p16_segs CK HW Bf4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b4_zlia)).
  pose proof CS as CS1. unfold bc_fl1, bc_saved in CS1. cbn [app] in CS1.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (kfr_seg al_rom frk csk rk mk s nc kf minv maxv FZ ltac:(lia) Bn1 ltac:(lia) Bf1 ltac:(lia) Bf3 Dnf Hmin Hmax
             ltac:(cell_from CS1) ltac:(cell_from CS1) ltac:(cell_from CS1) ltac:(cell_from CS1) ltac:(cell_from CS1)
             NCV SOKf KFO G2 G10 G8) |].
  intros fin (fr' & cs' & r' & M' & -> & FZ' & RI & KF' & H2' & H10' & H11' & H28' & H8' & AG & FK').
  assert (LR : local_regions C Ak A1 s [(kf, 1024%Z)]).
  { unfold local_regions.
    apply Forall_cons; [right; exists (Z_to_bv 64 kf), 1024%Z; rewrite u_Z2bv by lia; cbn [fst snd]; refine (conj Bf4 (conj Bf5 (conj Bf6 _))); lia|].
    apply Forall_nil. }
  destruct (rinv_WP2 C A1 Ak mk (with_vmmaps vmk md) M' _ s CK HW HSL Htop RI LR) as (W' & PM').
  apply (K fr' cs' M' r' FZ').
  - rewrite FK' by b4_rx. exact F8.
  - rewrite FK' by b4_rx. exact F9.
  - intros r Hr N8 N9 N18. rewrite (FK' r (b4_fs4 r Hr)). exact (FK r Hr N8 N9 N18).
  - exact W'.
  - exact (POSTMc_trans C A1 s (pixs + 20) 4 m1 mk M' PM (POSTMc_of_POSTM C A1 s (pixs + 20) 4 mk M' PM')).
  - assert (AG1 : agree_win (s - 320) 320 [] mk M').
    { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_nil. }
    keep_cells CS AG1 CSx. exact CSx.
  - rewrite (rinv_rdn SEGS _ mk M' (pixs + 20) 4 RI) by first [lia | b4_zlia | b4_dis]. exact R20.
  - assert (AGb : agree_win bil 104 [] mk M').
    { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_nil. }
    keep_cells CB AGb CBx. exact CBx.
  - intros j Hj. rewrite (rinv_rdn SEGS _ mk M' (nc + 4 * j) 4 RI) by first [lia | b4_zlia | b4_dis]. exact (NCV j Hj).
  - exact (b4_kidx_rinv [(kf, 1024%Z)] kx mk M' RI ltac:(lia) ltac:(lia) ltac:(b4_dis) KO).
  - exact KF'.
  - exact H2'.
  - exact H10'.
  - exact H11'.
  - exact H28'.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros r Hcs Hn. rewrite <- (GK r Hcs Hn). pose proof (b4_cs3 r Hcs Hn) as H3. cbn [In] in H3.
    destruct H3 as [<-|[<-|[<-|[]]]]; csr; reflexivity.
Qed.

Lemma bca_7 : forall frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx kf : Z) (S : TSet) (kR bR : Z),
  getr r1 4 = Z_to_bv 64 0x56270 ->
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> bc_blk C A1 Ak kf 1024 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf]) -> live Ak q = live A1 q) ->
  aroom Ak vmk (kR - 4) (bR - 4 * 131072) -> (6 <= kR)%Z -> (6 * 131072 <= bR)%Z -> bil <> nc -> bil <> kx -> nc <> kx -> bil <> kf -> nc <> kf -> kx <> kf -> (0 <= pixs < 2 ^ 64)%Z ->
  live A1 (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= maxv <= 255)%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> kfr_ok kf mk -> getr rk 2 = Z_to_bv 64 (s - 320) ->
  getr rk 10 = Z_to_bv 64 kf -> getr rk 11 = Z_to_bv 64 maxv -> getr rk 28 = Z_to_bv 64 11 -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall A' m' vm' r' (spat : Z),
     W C A' m' (with_vmmaps vm' md) -> sub_live A1 A' -> bc_blk C A1 A' bil 104 -> bc_blk C A1 A' nc 40 -> bc_blk C A1 A' kx 1024 -> bc_blk C A1 A' kf 1024 -> bc_blk C A1 A' spat 44 ->
     (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf; spat]) -> live A' q = live A1 q) -> aroom A' vm' (kR - 5) (bR - 5 * 131072) -> bil <> spat -> nc <> spat -> kx <> spat -> kf <> spat ->
     POSTMc C A1 s (pixs + 20) 4 m1 m' -> cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> kfr_ok kf m' -> getr r' 2 = Z_to_bv 64 (s - 320) ->
     getr r' 10 = Z_to_bv 64 spat -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP frk csk) r' (Z_to_bv 64 0x39de8) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39d98) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx kf S kR bR
    H4 CK Hs16 Hstk Htop FZ HW SL Bb Bn Bk Bf LQ AR HkR HbR Nbn Nbk Nnk Nbf Nnf Nkf Hp Lp Hmax PM CF R20 CB CN KI KF
    G2 G10 G11 G28 G22 G24 GK K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  pose proof Bb as (Gb1 & Gb2 & Gb3 & Lb & Nb & N0b).
  pose proof Bn as (Gn1 & Gn2 & Gn3 & Ln & Nn & N0n).
  pose proof Bk as (Gk1 & Gk2 & Gk3 & Lk & Nk & N0k).
  pose proof Bf as (Gf1 & Gf2 & Gf3 & Lf & Nf & N0f).
  pose proof (SL _ _ Lp) as Lpk.
  destruct (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW Lpk ltac:(lia)) as [Gp1 Gp2]. rewrite u_Z2bv in Gp1, Gp2 by lia.
  assert (Abk : b2_ap bil 104 kx 1024) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ bil kx 104 1024 CK HW Lb Lk Nbk); b2_clr; lia).
  assert (Abn : b2_ap bil 104 nc 40) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ bil nc 104 40 CK HW Lb Ln Nbn); b2_clr; lia).
  assert (Abf : b2_ap bil 104 kf 1024) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ bil kf 104 1024 CK HW Lb Lf Nbf); b2_clr; lia).
  assert (Anf : b2_ap nc 40 kf 1024) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ nc kf 40 1024 CK HW Ln Lf Nnf); b2_clr; lia).
  assert (Akf : b2_ap kx 1024 kf 1024) by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ kx kf 1024 1024 CK HW Lk Lf Nkf); b2_clr; lia).
  assert (Apb : b2_ap pixs 64 bil 104)
    by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ pixs bil 64 104 CK HW Lpk Lb); [intro E; rewrite E in Lp; congruence | b2_clr; lia ..]).
  assert (Apf : b2_ap pixs 64 kf 1024)
    by (unfold b2_ap; apply (exW_blk_apart C Ak mk _ pixs kf 64 1024 CK HW Lpk Lf); [intro E; rewrite E in Lp; congruence | b2_clr; lia ..]).
  b2_clr.
  pose proof CF as CF'. unfold bc_fl1, bc_saved in CF'. cbn [app] in CF'.
  assert (C304 : rdn SEGS mk (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil)) by cell_from CF'.
  clear CF'.
  assert (SOKf : store_ok SEGS mk (Z_to_bv 64 kf) 1024 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ kf 1024 kf 1024 p16_segs CK HW Lf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b2_zlia)).
  assert (SOKb : store_ok SEGS mk (Z_to_bv 64 (bil + 80)) 8 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ bil 104 (bil + 80) 8 p16_segs CK HW Lb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b2_zlia)).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_H2 al_rom (mkFP frk csk) rk mk s bil kf maxv ltac:(lia) Gb1 ltac:(lia) Gf1 ltac:(lia) Gf3 Abf Hmax C304 SOKf SOKb G2 G10 G11 G28 FZ) |].
  intros fin (r2 & M2 & -> & RI & RK1 & RB80 & Q1 & Q2 & Q10 & Q11 & AG).
  assert (WP2 : W C Ak M2 (with_vmmaps vmk md) /\ POSTM C A1 s mk M2).
  { apply (rinv_WP2 C A1 Ak mk _ M2 _ s CK HW SL Htop RI).
    unfold local_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; right; cbn [fst snd].
    - exists (Z_to_bv 64 kf), 1024%Z. rewrite u_Z2bv by lia. refine (conj Lf (conj Nf (conj N0f _))); lia.
    - exists (Z_to_bv 64 bil), 104%Z. rewrite u_Z2bv by lia. refine (conj Lb (conj Nb (conj N0b _))); lia. }
  destruct WP2 as [HW2 PM2].
  assert (AGf : agree_win (s - 320) 320 [] mk M2).
  { eapply agree_of_rinv; [exact RI|]. repeat apply Forall_cons; try apply Forall_nil; left; cbn [fst snd]; lia. }
  keep_cells CF AGf CF2.
  assert (AGb : agree_win bil 104 [(80%Z, 8%Z)] mk M2).
  { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [left; cbn [fst snd]; b2_alia|].
    apply Forall_cons; [right; exists (80%Z, 8%Z); split; [cbn [In]; auto | cbn [fst snd]; lia]|]. apply Forall_nil. }
  keep_cells CB AGb CB2.
  pose proof (cellsAt_app SEGS M2 bil _ [(80%Z, 8%nat, kf)] CB2
                (cellsAt_cons SEGS M2 bil [] 80 8 kf (bil + 80) eq_refl RB80 (cellsAt_nil SEGS M2 bil))) as CB2'.
  clear CB2.
  assert (R20b : rdn SEGS M2 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (rinv_rdn SEGS _ mk M2 (pixs + 20) 4 RI) by b2_rside. exact R20. }
  assert (CN2 : forall j, (0 <= j < 10)%Z -> rdn SEGS M2 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { intros j Hj. rewrite (rinv_rdn SEGS _ mk M2 (nc + 4 * j) 4 RI) by b2_rside. exact (CN j Hj). }
  assert (KI2 : kidx_ok kx M2).
  { intros v Hv. destruct (KI v Hv) as (kv & Rv & Hkv). exists kv. split; [|exact Hkv].
    rewrite (rinv_rdn SEGS _ mk M2 (kx + 4 * v) 4 RI) by b2_rside. exact Rv. }
  assert (KF2 : kfr_ok kf M2).
  { intros v Hv. destruct (Z.eq_dec v maxv) as [->|Nv].
    - eexists. split; [exact RK1 | exact FpSiteB.kfr_le1_one].
    - destruct (KF v Hv) as (x & Rv & Hx). exists x. split; [|exact Hx].
      rewrite (rinv_rdn SEGS _ mk M2 (kf + 4 * v) 4 RI) by b2_rside. exact Rv. }
  assert (Q4 : getr r2 4 = getr r1 4).
  { rewrite (AG 4%bv) by notin_lit. exact (GK 4%bv cs4 ltac:(notin_lit)). }
  rewrite H4 in Q4.
  assert (Hs16b : ((s - 320) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (RO : ret_ok (getr r2 1)) by (rewrite Q1; red; apply bv_eq; reflexivity).
  pose proof (LeptRoomBL.small_margin (11 * 4) ltac:(lia)) as SM.
  apply (W_calloc16_sure C Ak M2 _ r2 11 4 _ _ (getr r2 1) (s - 320) S CK HW2 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           AR ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) eq_refl
           RO Q4 Q2 Hs16b
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A3 m3 vm3 r3 res HW3 Hres CS3 Hnz L0 L1 L00 LEQ ZERO AL16 TOP PM3 AR3.
  rewrite ?with_vmmaps_twice in HW3 |- *.
  rewrite Q1.
  change (11 * 4)%Z with 44%Z in *.
  pose proof (bc_u64 res) as Ures.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (spat := u res) in *. clearbody spat. clear Hnz. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO. clear Eres.
  assert (AGf3 : agree_win (s - 320) 320 [] M2 m3)
    by exact (agree_of_FRM C (s - 320) M2 m3 (s - 320) 320 [] CK (proj1 PM3) ltac:(lia) ltac:(lia) ltac:(lia)).
  keep_cells CF2 AGf3 CF3.
  assert (AGb3 : agree_win bil 104 [] M2 m3)
    by exact (agree_of_LIVK Ak M2 m3 (Z_to_bv 64 bil) 104 bil 104 [] (proj2 PM3) Lb ltac:(b2_lside) ltac:(b2_lside)).
  keep_cells CB2' AGb3 CB3.
  assert (R20c : rdn SEGS m3 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (LIVK_rdn SEGS Ak M2 m3 (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PM3) Lpk) by b2_lside. exact R20b. }
  assert (CN3 : forall j, (0 <= j < 10)%Z -> rdn SEGS m3 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { intros j Hj. rewrite (LIVK_rdn SEGS Ak M2 m3 (Z_to_bv 64 nc) 40 (nc + 4 * j) 4 (proj2 PM3) Ln) by b2_lside. exact (CN2 j Hj). }
  assert (KI3 : kidx_ok kx m3).
  { intros v Hv. destruct (KI2 v Hv) as (kv & Rv & Hkv). exists kv. split; [|exact Hkv].
    rewrite (LIVK_rdn SEGS Ak M2 m3 (Z_to_bv 64 kx) 1024 (kx + 4 * v) 4 (proj2 PM3) Lk) by b2_lside. exact Rv. }
  assert (KF3 : kfr_ok kf m3).
  { intros v Hv. destruct (KF2 v Hv) as (x & Rv & Hx). exists x. split; [|exact Hx].
    rewrite (LIVK_rdn SEGS Ak M2 m3 (Z_to_bv 64 kf) 1024 (kf + 4 * v) 4 (proj2 PM3) Lf) by b2_lside. exact Rv. }
  assert (PM4 : POSTMc C A1 s (pixs + 20) 4 m1 m3).
  { apply (POSTMc_trans C A1 s (pixs + 20) 4 m1 mk m3 PM).
    apply (POSTMc_trans C A1 s (pixs + 20) 4 mk M2 m3).
    - apply POSTMc_of_POSTM. exact PM2.
    - apply POSTMc_of_POSTM. apply (POSTM_sub C A1 Ak s M2 m3 SL).
      apply (POSTM_mono C Ak (s - 320) s M2 m3); [lia | exact PM3]. }
  assert (LQ3 : forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf; spat]) -> live A3 q = live A1 q).
  { intros q Hq. rewrite LEQ by (intro E; apply Hq; subst q; cbn [map In]; tauto).
    apply LQ. intro Hin; apply Hq; cbn [map In] in Hin |- *; tauto. }
  apply (K A3 m3 vm3 r3 spat HW3 (sub_live_trans A1 Ak A3 SL (sub_live_new Ak A3 _ _ L0 L1 LEQ))
           (b2_blk_keep C A1 Ak A3 bil 104 _ Bb L0 LEQ) (b2_blk_keep C A1 Ak A3 nc 40 _ Bn L0 LEQ)
           (b2_blk_keep C A1 Ak A3 kx 1024 _ Bk L0 LEQ) (b2_blk_keep C A1 Ak A3 kf 1024 _ Bf L0 LEQ)
           (b2_blk_new C A1 Ak A3 m3 _ spat 44 CK HW3 SL L0 L1 L00 AL16 ltac:(lia) ltac:(lia)) LQ3).
  - b2_room AR3.
  - intro E; rewrite E in Lb; congruence.
  - intro E; rewrite E in Ln; congruence.
  - intro E; rewrite E in Lk; congruence.
  - intro E; rewrite E in Lf; congruence.
  - exact PM4.
  - exact CF3.
  - exact R20c.
  - exact CB3.
  - exact CN3.
  - exact KI3.
  - exact KF3.
  - csr; reflexivity.
  - exact Hres.
  - csr; reflexivity.
  - csr; reflexivity.
  - intros r CSr NIN. rewrite (cs_kept_get r2 r3 r CS3 CSr).
    rewrite (AG r) by (let H := fresh in intro H; apply (b2_cs_lo r CSr); cbn [In] in H |- *; tauto).
    exact (GK r CSr NIN).
Qed.

Local Ltac b5_zlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Local Ltac b5_nin := let H := fresh in intro H; cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H|]); exact H.
Local Ltac b5_nrx := let H := fresh in intro H; vm_compute in H; repeat (destruct H as [H|H]; [discriminate H|]); exact H.
Local Ltac b5_infs := vm_compute; repeat (first [left; reflexivity | right]).

Lemma b5_clr_any : forall C A m md (lo hi : Z), W C A m md -> (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  existsb (fun c => (fst c <=? lo) && (hi <=? snd c))%Z ll_clr = true ->
  forall i, (lo <= i < hi)%Z -> m (Z_to_bv 64 i) = None.
Proof.
  intros C A m md lo hi HW H0 H1 HE. apply existsb_exists in HE. destruct HE as ((clo & chi) & Hin & Hb).
  apply andb_true_iff in Hb. destruct Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. cbn [fst snd] in B1, B2.
  exact (exW_clr_None C A m md lo hi clo chi HW Hin B1 B2 H0 H1).
Qed.
Local Ltac b5_none HW := first [ exW_ro HW | (apply (b5_clr_any _ _ _ _ _ _ HW); [lia | lia | vm_compute; reflexivity]) ].

Lemma b5_postmc_0 : forall C A s c c' n m m', POSTMc C A s c' 0 m m' -> POSTMc C A s c n m m'.
Proof.
  intros C A s c c' n m m' PM. unfold POSTMc, LIVKc in *. destruct PM as [HF HL]. split; [exact HF|].
  intros q k i Hq Hi _. apply (HL q k i Hq Hi). lia.
Qed.

Lemma b5_rdn2 : forall (m M : word -> option byte) (a1 n1 a2 n2 z : Z) (n : nat),
  rinv [(a1, n1); (a2, n2)] m M -> (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z ->
  (z + Z.of_nat n <= a1 \/ a1 + n1 <= z)%Z -> (z + Z.of_nat n <= a2 \/ a2 + n2 <= z)%Z ->
  rdn SEGS M (Z_to_bv 64 z) n = rdn SEGS m (Z_to_bv 64 z) n.
Proof.
  intros m M a1 n1 a2 n2 z n RI H0 H1 D1 D2. apply (rinv_rdn SEGS _ m M z n RI H0 H1).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; assumption.
Qed.

Lemma b5_arr_keep : forall (P : Z -> Prop) (m M : word -> option byte) (a1 n1 a2 n2 b k : Z),
  rinv [(a1, n1); (a2, n2)] m M -> (0 <= b)%Z -> (b + 4 * k <= 2 ^ 64)%Z ->
  (b + 4 * k <= a1 \/ a1 + n1 <= b)%Z -> (b + 4 * k <= a2 \/ a2 + n2 <= b)%Z ->
  (forall i, (0 <= i < k)%Z -> exists x, rdn SEGS m (Z_to_bv 64 (b + 4 * i)) 4 = Some (Z_to_le_bytes 4 x) /\ P x) ->
  forall i, (0 <= i < k)%Z -> exists x, rdn SEGS M (Z_to_bv 64 (b + 4 * i)) 4 = Some (Z_to_le_bytes 4 x) /\ P x.
Proof.
  intros P m M a1 n1 a2 n2 b k RI H0 H1 D1 D2 HA i Hi.
  destruct (HA i Hi) as (x & Hx & Px). exists x. split; [|exact Px].
  rewrite (b5_rdn2 m M a1 n1 a2 n2 (b + 4 * i) 4 RI) by b5_zlia. exact Hx.
Qed.

Lemma b5_cs : forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv ->
  r = 3%bv \/ r = 4%bv \/ r = 27%bv.
Proof.
  intros r CS NI.
  assert (CR : In r cs_rest).
  { apply bc_cs_rest; [exact CS | | |]; intros E; apply NI; rewrite E; cbn [In]; repeat (first [left; reflexivity | right]). }
  unfold cs_rest in CR. cbn [In] in CR.
  repeat (destruct CR as [CR|CR]; [subst r; solve [ left; reflexivity | right; left; reflexivity | right; right; reflexivity
                                                   | exfalso; apply NI; cbn [In]; repeat (first [left; reflexivity | right]) ] |]).
  destruct CR.
Qed.

Lemma b5_fs_I : forall r : reg, In (u r) fs_list -> r <> 9%bv -> r <> 18%bv -> ~ In (ridx r) [9; 15; 18]%nat.
Proof.
  intros r Hr N9 N18 Hin. unfold fs_list in Hr. unfold ridx in Hin. cbn [In] in Hr, Hin.
  assert (U : bv_unsigned r = 9%Z \/ bv_unsigned r = 18%Z) by lia.
  destruct U as [U|U]; [apply N9 | apply N18]; apply bv_eq; rewrite U; reflexivity.
Qed.

Lemma b5_fs_K : forall r : reg, In (u r) fs_list -> r <> 8%bv -> ~ In (ridx r) [8; 14; 15]%nat.
Proof.
  intros r Hr N8 Hin. unfold fs_list in Hr. unfold ridx in Hin. cbn [In] in Hr, Hin.
  assert (U : bv_unsigned r = 8%Z) by lia.
  apply N8; apply bv_eq; rewrite U; reflexivity.
Qed.

Definition b5_ap (p n q k : Z) : Prop := (p + n <= q \/ q + k <= p)%Z.

Lemma b5_apart : forall C A1 A m md (p q n k : Z), Cok C -> W C A m md -> bc_blk C A1 A p n -> bc_blk C A1 A q k -> p <> q ->
  (0 <= n)%Z -> (0 <= k)%Z -> b5_ap p n q k.
Proof.
  intros C A1 A m md p q n k CK HW Bp Bq Npq Hn Hk. pose proof CK as [Ctop Csp0 _ _ _]. pose proof LSTK_val as LS.
  pose proof (bc_u64 (c_sp0 C)) as U.
  destruct Bp as (P1 & P2 & _ & P4 & _ & _). destruct Bq as (Q1 & Q2 & _ & Q4 & _ & _).
  exact (exW_blk_apart C A m md p q n k CK HW P4 Q4 Npq ltac:(lia) ltac:(lia) Hn Hk).
Qed.

Lemma b5_apart_px : forall C A1 A m md (p n x : Z), Cok C -> W C A m md -> sub_live A1 A -> bc_blk C A1 A p n ->
  live A1 (Z_to_bv 64 x) = Some 64%Z -> (0 <= x < 2 ^ 64)%Z -> (0 <= n)%Z ->
  b5_ap p n x 64 /\ (4096 <= x)%Z /\ (x + 64 <= alloc_top (c_vm C))%Z.
Proof.
  intros C A1 A m md p n x CK HW SL Bp Lx Hx Hn. pose proof CK as [Ctop Csp0 _ _ _]. pose proof LSTK_val as LS.
  pose proof (bc_u64 (c_sp0 C)) as U.
  destruct Bp as (P1 & P2 & _ & P4 & P5 & _).
  assert (Lx' : live A (Z_to_bv 64 x) = Some 64%Z) by exact (SL _ _ Lx).
  assert (Npx : p <> x) by (intros E; rewrite E in P5; congruence).
  pose proof (blk_range C A m md (Z_to_bv 64 x) 64 CK HW Lx' ltac:(lia)) as BR. rewrite u_Z2bv in BR by lia.
  split; [exact (exW_blk_apart C A m md p x n 64 CK HW P4 Lx' Npx ltac:(lia) Hx Hn ltac:(lia)) | lia].
Qed.

Lemma bca_8 : forall fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx kf spat : Z) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> reg_get frk 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get frk 9 = Z_to_bv 64 0xffffffff40a00000 ->
  (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get frk r = reg_get fr r) -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> bc_blk C A1 Ak kf 1024 -> bc_blk C A1 Ak spat 44 -> bil <> nc -> bil <> kx -> nc <> kx -> bil <> kf -> nc <> kf -> kx <> kf -> bil <> spat ->
  nc <> spat -> kx <> spat -> kf <> spat -> (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> kfr_ok kf mk -> getr rk 2 = Z_to_bv 64 (s - 320) ->
  getr rk 10 = Z_to_bv 64 spat -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall fr' cs' m' r',
     frm_zero cs' -> reg_get fr' 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get fr' 9 = Z_to_bv 64 0xffffffff42480000 -> reg_get fr' 18 = Z_to_bv 64 0x4024000000000000 ->
     (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r) -> W C Ak m' (with_vmmaps vmk md) -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> kfr_ok kf m' -> kcell_ok spat 11 m' ->
     getr r' 2 = Z_to_bv 64 (s - 320) -> getr r' 20 = Z_to_bv 64 1 -> getr r' 21 = Z_to_bv 64 spat -> getr r' 22 = Z_to_bv 64 1 -> getr r' 24 = Z_to_bv 64 pixs ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r' (Z_to_bv 64 0x39e68) m' al_rom) (with_vmmaps vmk md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39de8) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx kf spat S
    CK Hs16 Hstk Htop FZ F8 F9 FK HW SL Bb Bn Bx Bf Bs Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs Hp Lp PM CLf R20 CLb NC KX KF
    G2 G10 G22 G24 GCS K.
  pose proof (b5_apart_px C A1 Ak mk _ spat 44 pixs CK HW SL Bs Lp Hp ltac:(exW_cmp)) as (Dp & Px1 & Px2).
  pose proof (b5_apart C A1 Ak mk _ spat bil 44 104 CK HW Bs Bb (fun E => Nbs (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Db.
  pose proof (b5_apart C A1 Ak mk _ spat nc 44 40 CK HW Bs Bn (fun E => Nns (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Dn.
  pose proof (b5_apart C A1 Ak mk _ spat kx 44 1024 CK HW Bs Bx (fun E => Nxs (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Dx.
  pose proof (b5_apart C A1 Ak mk _ spat kf 44 1024 CK HW Bs Bf (fun E => Nfs (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Df.
  clear Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs Hs16.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. clear Cal.
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  cbv [ll_img LLU16 snd] in Cimg.
  destruct Bs as (Bs1 & Bs2 & Bs3 & Bs4 & Bs5 & Bs6).
  pose proof CLf as CLx. unfold bc_fl1, bc_saved in CLx. cbn [app] in CLx.
  assert (R272 : rdn SEGS mk (Z_to_bv 64 (s - 272)) 8 = Some (Z_to_le_bytes 8 11)) by cell_from CLx.
  clear CLx.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_I al_rom frk csk rk mk s spat FZ ltac:(lia) Bs1 ltac:(lia) Bs3 R272 G2 G10 F9) |].
  intros fin (fr1 & cs1 & r2 & -> & FZ1 & I2 & I8 & I9 & I18 & I19 & I20 & I21 & I23 & AG1 & FI9 & FI18 & FIK).
  assert (SOKa : store_ok SEGS mk (Z_to_bv 64 spat) 44 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ spat 44 spat 44 p16_segs CK HW Bs4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b5_zlia)).
  assert (SOKs : store_ok SEGS mk (Z_to_bv 64 (s - 336)) 16 = true) by (apply (W_sok_win C Ak mk _ (s - 336) 16 CK HW); b5_zlia).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    refine (SpL_seg al_rom fr1 cs1 r2 mk s spat FZ1 _ Bs1 _ Bs3 SOKa SOKs _ _ I2 I8 I9 I18 I19 I20 I21 I23 FI9);
    [lia | lia | b5_none HW | b5_none HW] |].
  intros fin (fr2 & cs2 & r3 & M & -> & FZ2 & RI & KC & J2 & J8 & J9 & J18 & J19 & J20 & J21 & J23 & AG2 & FS2).
  unfold regs_agree in AG1, AG2. cbv beta in AG1, AG2.
  destruct Bb as (Bb1 & Bb2 & _ & Bb4 & _ & _).
  destruct Bn as (Bn1 & Bn2 & _ & Bn4 & _ & _).
  destruct Bx as (Bx1 & Bx2 & _ & Bx4 & _ & _).
  destruct Bf as (Bf1 & Bf2 & _ & Bf4 & _ & _).
  assert (WP : W C Ak M (with_vmmaps vmk md) /\ POSTMc C A1 s spat 0 mk M).
  { apply (rinv_WPc C A1 Ak mk (with_vmmaps vmk md) M [(spat, 44%Z); ((s - 336)%Z, 16%Z)] s spat 0%Z (Z_to_bv 64 spat) 44%Z);
      try first [exact CK | exact HW | exact SL | exact Htop | exact Bs4 | exact Bs6 | exact RI | (rewrite u_Z2bv by lia; lia)].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - right; right. exists (Z_to_bv 64 spat), 44%Z. rewrite u_Z2bv by lia. refine (conj Bs4 (conj Bs5 (conj Bs6 (conj _ _)))); lia.
    - left; lia. }
  destruct WP as [W2 PM2].
  assert (PM' : POSTMc C A1 s (pixs + 20) 4 m1 M) by exact (POSTMc_trans _ _ _ _ _ _ _ _ PM (b5_postmc_0 _ _ _ _ _ _ _ _ PM2)).
  assert (AGf : agree_win (s - 320) 320 [] mk M).
  { eapply agree_of_rinv; [exact RI|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; lia. }
  keep_cells CLf AGf CLf'.
  assert (AGb : agree_win bil 104 [] mk M).
  { unfold b5_ap in Db. eapply agree_of_rinv; [exact RI|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; lia. }
  keep_cells CLb AGb CLb'.
  assert (R20' : rdn SEGS M (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { unfold b5_ap in Dp. rewrite (b5_rdn2 mk M spat 44 (s - 336) 16 (pixs + 20) 4 RI) by b5_zlia. exact R20. }
  assert (NC' : forall j, (0 <= j < 10)%Z -> rdn SEGS M (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { unfold b5_ap in Dn. intros j Hj. rewrite (b5_rdn2 mk M spat 44 (s - 336) 16 (nc + 4 * j) 4 RI) by b5_zlia. exact (NC j Hj). }
  assert (KX' : kidx_ok kx M)
    by (unfold b5_ap in Dx; exact (b5_arr_keep (fun kv => (0 <= kv <= 8)%Z) mk M spat 44 (s - 336) 16 kx 256 RI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KX)).
  assert (KF' : kfr_ok kf M)
    by (unfold b5_ap in Df; exact (b5_arr_keep FpSiteB.kfr_le1 mk M spat 44 (s - 336) 16 kf 256 RI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KF)).
  refine (K fr2 cs2 M r3 FZ2 _ _ _ _ W2 PM' CLf' R20' CLb' NC' KX' KF' KC J2 J20 J21 _ _ _).
  - rewrite FS2 by b5_infs. rewrite FIK by b5_nrx. exact F8.
  - rewrite FS2 by b5_infs. exact FI9.
  - rewrite FS2 by b5_infs. exact FI18.
  - intros r Hr N8 N9 N18. rewrite (FS2 r Hr), (FIK r (b5_fs_I r Hr N9 N18)). exact (FK r Hr N8 N9 N18).
  - rewrite AG2 by b5_nin. rewrite AG1 by b5_nin. exact G22.
  - rewrite AG2 by b5_nin. rewrite AG1 by b5_nin. exact G24.
  - intros r CS NI. destruct (b5_cs r CS NI) as [-> | [-> | ->]];
      rewrite AG2 by b5_nin; rewrite AG1 by b5_nin; apply GCS; assumption.
Qed.

Local Ltac b3_zlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Lemma b3_cells_l : forall m b L1 L2, cellsAt SEGS m b (L1 ++ L2) -> cellsAt SEGS m b L1.
Proof. intros m b L1 L2 H. unfold cellsAt in *. apply Forall_app in H. exact (proj1 H). Qed.

Lemma b3_cells_r : forall m b L1 L2, cellsAt SEGS m b (L1 ++ L2) -> cellsAt SEGS m b L2.
Proof. intros m b L1 L2 H. unfold cellsAt in *. apply Forall_app in H. exact (proj2 H). Qed.

Lemma b3_rd1 : forall M M' (a w z : Z) (n : nat), rinv [(a, w)] M M' -> (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z ->
  (z + Z.of_nat n <= a \/ a + w <= z)%Z -> rdn SEGS M' (Z_to_bv 64 z) n = rdn SEGS M (Z_to_bv 64 z) n.
Proof.
  intros M M' a w z n RI H0 H1 H2. apply (rinv_rdn SEGS [(a, w)] M M' z n RI H0 H1).
  intros r Hr. destruct Hr as [<-|[]]. exact H2.
Qed.

Lemma b3_kidx_keep : forall kx M M', (forall v, (0 <= v < 256)%Z -> rdn SEGS M' (Z_to_bv 64 (kx + 4 * v)) 4 = rdn SEGS M (Z_to_bv 64 (kx + 4 * v)) 4) ->
  kidx_ok kx M -> kidx_ok kx M'.
Proof. intros kx M M' E K v Hv. destruct (K v Hv) as (x & Hx & Hb). exists x. rewrite E by exact Hv. exact (conj Hx Hb). Qed.

Lemma b3_kfr_keep : forall kf M M', (forall v, (0 <= v < 256)%Z -> rdn SEGS M' (Z_to_bv 64 (kf + 4 * v)) 4 = rdn SEGS M (Z_to_bv 64 (kf + 4 * v)) 4) ->
  kfr_ok kf M -> kfr_ok kf M'.
Proof. intros kf M M' E K v Hv. destruct (K v Hv) as (x & Hx & Hb). exists x. rewrite E by exact Hv. exact (conj Hx Hb). Qed.

Lemma b3_kcell_keep : forall arr n M M', (forall i, (0 <= i < n)%Z -> rdn SEGS M' (Z_to_bv 64 (arr + 4 * i)) 4 = rdn SEGS M (Z_to_bv 64 (arr + 4 * i)) 4) ->
  kcell_ok arr n M -> kcell_ok arr n M'.
Proof. intros arr n M M' E K i Hi. destruct (K i Hi) as (x & Hx & Hb). exists x. rewrite E by exact Hi. exact (conj Hx Hb). Qed.

Lemma b3_cs_n1_10 : forall r : reg, AllocIface.callee_saved r -> ~ In r [1; 10]%bv.
Proof.
  intros r CSr. destruct (cs_cases r CSr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; notin_lit.
Qed.

Lemma b3_cs_nJ : forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> ~ In r [1; 8; 10; 11]%bv.
Proof.
  intros r CSr NI. destruct (cs_cases r CSr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    first [notin_lit | (exfalso; apply NI; in_lit)].
Qed.

Lemma b3_blk_step : forall C A1 A A' (res : word) (X n : Z), bc_blk C A1 A X n -> live A res = None ->
  (forall q, q <> res -> live A' q = live A q) -> bc_blk C A1 A' X n.
Proof.
  intros C A1 A A' res X n (G & T & M & L & L1 & L0) LN LEQ. refine (conj G (conj T (conj M (conj _ (conj L1 L0))))).
  rewrite LEQ; [exact L|]. intros E. rewrite E, LN in L. discriminate.
Qed.

Lemma b3_blk_new : forall C A1 A A' m md (res : word) (n : Z), Cok C -> W C A' m md -> sub_live A1 A -> live A res = None ->
  live A' res = Some n -> live (c_A0 C) res = None -> (u res mod 16 = 0)%Z -> (0 < n)%Z -> bc_blk C A1 A' (u res) n.
Proof.
  intros C A1 A A' m md res n CK HW SL LN L' L0 HA16 Hn.
  pose proof (blk_range C A' m md res n CK HW L' Hn) as [G T].
  unfold bc_blk. rewrite Z_to_bv_bv_unsigned. refine (conj G (conj T (conj HA16 (conj L' (conj _ L0))))).
  destruct (live A1 res) as [k|] eqn:E; [|reflexivity]. rewrite (SL _ _ E) in LN. discriminate.
Qed.

Lemma b3_ne_new : forall C A1 A (res : word) (X n : Z), bc_blk C A1 A X n -> live A res = None -> X <> u res.
Proof. intros C A1 A res X n (_ & _ & _ & L & _) LN E. rewrite E, Z_to_bv_bv_unsigned, LN in L. discriminate. Qed.

Definition b3_ap (x n y k : Z) : Prop := (x + n <= y \/ y + k <= x)%Z.

Lemma b3_apart : forall C A1 A m md (X Y n k : Z), Cok C -> W C A m md -> bc_blk C A1 A X n -> bc_blk C A1 A Y k -> X <> Y ->
  (0 <=? n)%Z = true -> (0 <=? k)%Z = true -> b3_ap X n Y k.
Proof.
  intros C A1 A m md X Y n k CK HW (GX & TX & _ & LX & _) (GY & TY & _ & LY & _) NE Hn Hk.
  apply Z.leb_le in Hn. apply Z.leb_le in Hk. pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  unfold b3_ap. exact (exW_blk_apart C A m md X Y n k CK HW LX LY NE ltac:(lia) ltac:(lia) Hn Hk).
Qed.

Lemma bca_9 : forall frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx kf spat : Z) (S : TSet) (kR bR : Z),
  getr r1 4 = Z_to_bv 64 0x56270 ->
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> bc_blk C A1 Ak kf 1024 -> bc_blk C A1 Ak spat 44 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf; spat]) -> live Ak q = live A1 q) ->
  aroom Ak vmk (kR - 5) (bR - 5 * 131072) -> (6 <= kR)%Z -> (6 * 131072 <= bR)%Z -> bil <> nc -> bil <> kx -> nc <> kx -> bil <> kf -> nc <> kf -> kx <> kf -> bil <> spat -> nc <> spat -> kx <> spat ->
  kf <> spat -> (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> kfr_ok kf mk -> kcell_ok spat 11 mk ->
  getr rk 2 = Z_to_bv 64 (s - 320) -> getr rk 20 = Z_to_bv 64 1 -> getr rk 21 = Z_to_bv 64 spat -> getr rk 22 = Z_to_bv 64 1 -> getr rk 24 = Z_to_bv 64 pixs ->
  (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall A' m' vm' r' (rng : Z),
     W C A' m' (with_vmmaps vm' md) -> sub_live A1 A' -> bc_blk C A1 A' bil 104 -> bc_blk C A1 A' nc 40 -> bc_blk C A1 A' kx 1024 -> bc_blk C A1 A' kf 1024 -> bc_blk C A1 A' spat 44 ->
     bc_blk C A1 A' rng 1024 -> (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf; spat; rng]) -> live A' q = live A1 q) -> aroom A' vm' (kR - 6) (bR - 6 * 131072) -> bil <> rng -> nc <> rng ->
     kx <> rng -> kf <> rng -> spat <> rng -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf); (32%Z, 8%nat, spat)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> kfr_ok kf m' -> kcell_ok spat 11 m' ->
     getr r' 2 = Z_to_bv 64 (s - 320) -> getr r' 10 = Z_to_bv 64 rng -> getr r' 8 = Z_to_bv 64 256 -> getr r' 20 = Z_to_bv 64 1 -> getr r' 21 = Z_to_bv 64 spat -> getr r' 22 = Z_to_bv 64 1 ->
     getr r' 24 = Z_to_bv 64 pixs -> (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP frk csk) r' (Z_to_bv 64 0x39e80) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39e68) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx kf spat S kR bR
    H4 CK Hs16 Hstk Htop FZ HW SL Bb Bn Bx Bf Bs LQ AR HkR HbR Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs Hpx Lpx PM CS R20 CB NC KI KF KS
    H2 H20 H21 H22 H24 HCS K.
  pose proof (b3_apart C A1 Ak mk _ bil nc 104 40 CK HW Bb Bn Nbn eq_refl eq_refl) as Abn.
  pose proof (b3_apart C A1 Ak mk _ bil kx 104 1024 CK HW Bb Bx Nbx eq_refl eq_refl) as Abx.
  pose proof (b3_apart C A1 Ak mk _ bil kf 104 1024 CK HW Bb Bf Nbf eq_refl eq_refl) as Abf.
  pose proof (b3_apart C A1 Ak mk _ bil spat 104 44 CK HW Bb Bs Nbs eq_refl eq_refl) as Abs.
  clear Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof Bb as (Gb & Tb & _ & Lb & Lb1 & Lb0).
  pose proof Bn as (Gn & Tn & _ & Ln & _ & _).
  pose proof Bx as (Gx & Tx & _ & Lx & _ & _).
  pose proof Bf as (Gf & Tf & _ & Lf & _ & _).
  pose proof Bs as (Gs & Ts & _ & Ls & _ & _).
  assert (LpK : live Ak (Z_to_bv 64 pixs) = Some 64%Z) by (apply SL; exact Lpx).
  pose proof (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW LpK ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  pose proof (b3_cells_r _ _ _ _ CS) as CSt.
  assert (C304 : rdn SEGS mk (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil)) by cell_from CSt.
  assert (SOK : store_ok SEGS mk (Z_to_bv 64 (bil + 32)) 8 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ bil 104 (bil + 32) 8 p16_segs CK HW Lb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b3_zlia)).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_J al_rom (mkFP frk csk) rk mk s bil spat ltac:(lia) Gb ltac:(lia) ltac:(lia) C304 SOK H2 H21 FZ) |].
  intros fin (rJ & MJ & -> & RI & CSP & J1 & J2 & J10 & J11 & J8 & AGJ).
  assert (FRS : fresh_regions C Ak A1 [((bil + 32)%Z, 8%Z)]).
  { unfold fresh_regions. apply Forall_cons; [|apply Forall_nil]. exists (Z_to_bv 64 bil), 104%Z. cbn [fst snd]. rewrite u_Z2bv by lia.
    refine (conj Lb (conj Lb1 (conj Lb0 (conj _ _)))); lia. }
  destruct (rinv_WP C A1 Ak mk _ MJ _ s CK HW SL Htop RI FRS) as [WJ PMJ].
  assert (J4 : getr rk 4 = getr r1 4) by (apply HCS; [exact cs4 | notin_lit]).
  apply (W_calloc16_sure (fx := mkFP frk csk) C Ak MJ _ rJ 256 4 (kR - 5) _ _ (s - 320) S CK WJ J10 J11 ltac:(lia) ltac:(lia) ltac:(lia) AR ltac:(lia)
           ltac:(rewrite (alloc_margin_small (256 * 4)) by lia; lia) ltac:(unfold ROOM_NMAX; lia) J1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) J2 (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r2 res W2 Hres CS2 Hnz L1 L2 L00 LEQ ZERO AL16 TOP PM2 HRM2.
  rewrite with_vmmaps_twice in W2 |- *.
  change (256 * 4)%Z with 1024%Z in L2.
  clear Hnz.
  assert (SL2 : sub_live A1 A2) by exact (sub_live_trans A1 Ak A2 SL (sub_live_new Ak A2 res _ L1 L2 LEQ)).
  assert (LQ2 : forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf; spat; u res]) -> live A2 q = live A1 q).
  { intros q NI. rewrite LEQ.
    - apply LQ. intros I. apply NI. cbn [map In] in *. tauto.
    - intros E. apply NI. subst q. cbn [map In]. rewrite Z_to_bv_bv_unsigned. tauto. }
  assert (AR2 : aroom A2 vm2 (kR - 6) (bR - 6 * 2 ^ 17)).
  { eapply aroom_mono; [exact HRM2 | |]; rewrite ?(alloc_margin_small (256 * 4)) by lia; lia. }
  assert (PMc : POSTMc C A1 s (pixs + 20) 4 m1 m2).
  { apply (POSTMc_trans _ _ _ _ _ m1 mk m2 PM). apply (POSTMc_trans _ _ _ _ _ mk MJ m2 (POSTMc_of_POSTM _ _ _ _ _ _ _ PMJ)).
    apply (POSTMc_sub C A1 Ak s (pixs + 20) 4 MJ m2 SL). apply (POSTMc_mono C Ak (s - 320) s (pixs + 20) 4 MJ m2); [lia|].
    exact (POSTMc_of_POSTM _ _ _ _ _ _ _ PM2). }
  assert (AGs1 : agree_win (s - 320) 320 [] mk MJ).
  { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [|apply Forall_nil]. left. cbn [fst snd]. lia. }
  keep_cells CS AGs1 CSJ.
  pose proof (agree_of_FRM C (s - 320) MJ m2 (s - 320) 320 [] CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia)) as AGs2.
  keep_cells CSJ AGs2 CS2'.
  assert (R20' : rdn SEGS m2 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (LIVK_rdn SEGS Ak MJ m2 (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PM2) LpK) by (rewrite u_Z2bv by lia; b3_zlia).
    rewrite (LIVK_rdn SEGS A1 mk MJ (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PMJ) Lpx) by (rewrite u_Z2bv by lia; b3_zlia). exact R20. }
  assert (AGb : agree_win bil 104 [(32%Z, 8%Z)] mk MJ).
  { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [|apply Forall_nil]. right. exists (32%Z, 8%Z).
    split; [left; reflexivity|]. cbn [fst snd]. lia. }
  keep_cells CB AGb CBJ.
  pose proof (agree_of_LIVK Ak MJ m2 (Z_to_bv 64 bil) 104 bil 104 [] (proj2 PM2) Lb ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)) as AGb2.
  keep_cells CBJ AGb2 CB2a.
  assert (CSP2 : rdn SEGS m2 (Z_to_bv 64 (bil + 32)) 8 = Some (Z_to_le_bytes 8 spat)).
  { rewrite (LIVK_rdn SEGS Ak MJ m2 (Z_to_bv 64 bil) 104 (bil + 32) 8 (proj2 PM2) Lb) by (rewrite u_Z2bv by lia; b3_zlia). exact CSP. }
  pose proof (cellsAt_app SEGS m2 bil _ _ CB2a (cellsAt_cons SEGS m2 bil [] 32 8 spat (bil + 32) eq_refl CSP2 (cellsAt_nil SEGS m2 bil))) as CB2.
  assert (NC' : forall j, (0 <= j < 10)%Z -> rdn SEGS m2 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { unfold b3_ap in Abn. intros j Hj. rewrite (LIVK_rdn SEGS Ak MJ m2 (Z_to_bv 64 nc) 40 (nc + 4 * j) 4 (proj2 PM2) Ln) by (rewrite u_Z2bv by lia; b3_zlia).
    rewrite (b3_rd1 mk MJ (bil + 32) 8 (nc + 4 * j) 4 RI) by b3_zlia. exact (NC j Hj). }
  assert (KI' : kidx_ok kx m2).
  { unfold b3_ap in Abx. apply (b3_kidx_keep kx mk m2); [|exact KI]. intros v Hv.
    rewrite (LIVK_rdn SEGS Ak MJ m2 (Z_to_bv 64 kx) 1024 (kx + 4 * v) 4 (proj2 PM2) Lx) by (rewrite u_Z2bv by lia; b3_zlia).
    apply (b3_rd1 mk MJ (bil + 32) 8 _ 4 RI); b3_zlia. }
  assert (KF' : kfr_ok kf m2).
  { unfold b3_ap in Abf. apply (b3_kfr_keep kf mk m2); [|exact KF]. intros v Hv.
    rewrite (LIVK_rdn SEGS Ak MJ m2 (Z_to_bv 64 kf) 1024 (kf + 4 * v) 4 (proj2 PM2) Lf) by (rewrite u_Z2bv by lia; b3_zlia).
    apply (b3_rd1 mk MJ (bil + 32) 8 _ 4 RI); b3_zlia. }
  assert (KS' : kcell_ok spat 11 m2).
  { unfold b3_ap in Abs. apply (b3_kcell_keep spat 11 mk m2); [|exact KS]. intros v Hv.
    rewrite (LIVK_rdn SEGS Ak MJ m2 (Z_to_bv 64 spat) 44 (spat + 4 * v) 4 (proj2 PM2) Ls) by (rewrite u_Z2bv by lia; b3_zlia).
    apply (b3_rd1 mk MJ (bil + 32) 8 _ 4 RI); b3_zlia. }
  refine (K A2 m2 vm2 r2 (u res) W2 SL2 (b3_blk_step C A1 Ak A2 res bil 104 Bb L1 LEQ) (b3_blk_step C A1 Ak A2 res nc 40 Bn L1 LEQ)
            (b3_blk_step C A1 Ak A2 res kx 1024 Bx L1 LEQ) (b3_blk_step C A1 Ak A2 res kf 1024 Bf L1 LEQ) (b3_blk_step C A1 Ak A2 res spat 44 Bs L1 LEQ)
            (b3_blk_new C A1 Ak A2 m2 _ res 1024 CK W2 SL L1 L2 L00 AL16 ltac:(lia)) LQ2 AR2
            (b3_ne_new C A1 Ak res bil 104 Bb L1) (b3_ne_new C A1 Ak res nc 40 Bn L1) (b3_ne_new C A1 Ak res kx 1024 Bx L1)
            (b3_ne_new C A1 Ak res kf 1024 Bf L1) (b3_ne_new C A1 Ak res spat 44 Bs L1)
            PMc CS2' R20' CB2 NC' KI' KF' KS' _ _ _ _ _ _ _ _).
  all: try (csr; reflexivity).
  - rewrite Hres. symmetry. apply Z_to_bv_bv_unsigned.
  - intros r CSr NI. rewrite (cs_kept_get rJ r2 r CS2 CSr). rewrite (AGJ r) by (apply b3_cs_nJ; assumption). apply HCS; assumption.
Qed.

Lemma bca_10 : forall fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx kf spat rng : Z) (S : TSet),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> reg_get frk 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get frk 9 = Z_to_bv 64 0xffffffff42480000 ->
  reg_get frk 18 = Z_to_bv 64 0x4024000000000000 -> (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get frk r = reg_get fr r) -> W C Ak mk (with_vmmaps vmk md) ->
  sub_live A1 Ak -> bc_blk C A1 Ak bil 104 -> bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> bc_blk C A1 Ak kf 1024 -> bc_blk C A1 Ak spat 44 -> bc_blk C A1 Ak rng 1024 -> bil <> nc -> bil <> kx ->
  nc <> kx -> bil <> kf -> nc <> kf -> kx <> kf -> bil <> spat -> nc <> spat -> kx <> spat -> kf <> spat -> bil <> rng -> nc <> rng -> kx <> rng -> kf <> rng -> spat <> rng -> (0 <= pixs < 2 ^ 64)%Z ->
  live A1 (Z_to_bv 64 pixs) = Some 64%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf); (32%Z, 8%nat, spat)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> kfr_ok kf mk -> kcell_ok spat 11 mk ->
  getr rk 2 = Z_to_bv 64 (s - 320) -> getr rk 10 = Z_to_bv 64 rng -> getr rk 8 = Z_to_bv 64 256 -> getr rk 20 = Z_to_bv 64 1 -> getr rk 21 = Z_to_bv 64 spat -> getr rk 22 = Z_to_bv 64 1 ->
  getr rk 24 = Z_to_bv 64 pixs -> (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) ->
  (forall fr' cs' m' r',
     frm_zero cs' -> reg_get fr' 8 = Z_to_bv 64 0xffffffff43480000 -> reg_get fr' 9 = Z_to_bv 64 0xffffffff42480000 -> reg_get fr' 18 = Z_to_bv 64 0x4024000000000000 ->
     (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r) -> W C Ak m' (with_vmmaps vmk md) -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m' bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf); (32%Z, 8%nat, spat)] ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> kfr_ok kf m' -> kcell_ok spat 11 m' -> kcell_ok rng 256 m' ->
     getr r' 2 = Z_to_bv 64 (s - 320) -> getr r' 8 = Z_to_bv 64 256 -> getr r' 9 = Z_to_bv 64 256 -> getr r' 18 = Z_to_bv 64 1 -> getr r' 19 = Z_to_bv 64 1 -> getr r' 20 = Z_to_bv 64 1 ->
     getr r' 21 = Z_to_bv 64 spat -> getr r' 22 = Z_to_bv 64 1 -> getr r' 23 = Z_to_bv 64 rng -> getr r' 24 = Z_to_bv 64 pixs -> getr r' 25 = Z_to_bv 64 (rng + 1024) ->
     getr r' 26 = Z_to_bv 64 (rng + 1024) -> (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r' (Z_to_bv 64 0x39eec) m' al_rom) (with_vmmaps vmk md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39e80) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros fr frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx kf spat rng S
    CK Hs16 Hstk Htop FZ F8 F9 F18 FK HW SL Bb Bn Bx Bf Bs Br Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs Nbr Nnr Nxr Nfr Nsr Hp Lp PM
    CLf R20 CLb NC KX KF KS G2 G10 G8 G20 G21 G22 G24 GCS K.
  pose proof (b5_apart_px C A1 Ak mk _ rng 1024 pixs CK HW SL Br Lp Hp ltac:(exW_cmp)) as (Dp & Px1 & Px2).
  pose proof (b5_apart C A1 Ak mk _ rng bil 1024 104 CK HW Br Bb (fun E => Nbr (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Db.
  pose proof (b5_apart C A1 Ak mk _ rng nc 1024 40 CK HW Br Bn (fun E => Nnr (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Dn.
  pose proof (b5_apart C A1 Ak mk _ rng kx 1024 1024 CK HW Br Bx (fun E => Nxr (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Dx.
  pose proof (b5_apart C A1 Ak mk _ rng kf 1024 1024 CK HW Br Bf (fun E => Nfr (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Df.
  pose proof (b5_apart C A1 Ak mk _ rng spat 1024 44 CK HW Br Bs (fun E => Nsr (eq_sym E)) ltac:(exW_cmp) ltac:(exW_cmp)) as Ds.
  clear Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs Nbr Nnr Nxr Nfr Nsr Hs16.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. clear Cal.
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  cbv [ll_img LLU16 snd] in Cimg.
  destruct Br as (Br1 & Br2 & Br3 & Br4 & Br5 & Br6).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_K al_rom frk csk rk mk s rng FZ ltac:(lia) Br1 ltac:(lia) Br3 G2 G10 G8 F8) |].
  intros fin (fr1 & cs1 & r2 & -> & FZ1 & I2 & I8 & I9 & I18 & I19 & I23 & I25 & I26 & AG1 & FI8 & FIK).
  assert (SOKa : store_ok SEGS mk (Z_to_bv 64 rng) 1024 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ rng 1024 rng 1024 p16_segs CK HW Br4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b5_zlia)).
  assert (SOKs : store_ok SEGS mk (Z_to_bv 64 (s - 336)) 16 = true) by (apply (W_sok_win C Ak mk _ (s - 336) 16 CK HW); b5_zlia).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    refine (RgL_seg al_rom fr1 cs1 r2 mk s rng FZ1 _ Br1 _ Br3 SOKa SOKs _ _ I2 I8 I9 I18 I19 I23 I25 I26 FI8);
    [lia | lia | b5_none HW | b5_none HW] |].
  intros fin (fr2 & cs2 & r3 & M & -> & FZ2 & RI & KC & J2 & J8 & J9 & J18 & J19 & J23 & J25 & J26 & AG2 & FS2).
  unfold regs_agree in AG1, AG2. cbv beta in AG1, AG2.
  destruct Bb as (Bb1 & Bb2 & _ & Bb4 & _ & _).
  destruct Bn as (Bn1 & Bn2 & _ & Bn4 & _ & _).
  destruct Bx as (Bx1 & Bx2 & _ & Bx4 & _ & _).
  destruct Bf as (Bf1 & Bf2 & _ & Bf4 & _ & _).
  destruct Bs as (Bs1 & Bs2 & _ & Bs4 & _ & _).
  assert (WP : W C Ak M (with_vmmaps vmk md) /\ POSTMc C A1 s rng 0 mk M).
  { apply (rinv_WPc C A1 Ak mk (with_vmmaps vmk md) M [(rng, 1024%Z); ((s - 336)%Z, 16%Z)] s rng 0%Z (Z_to_bv 64 rng) 1024%Z);
      try first [exact CK | exact HW | exact SL | exact Htop | exact Br4 | exact Br6 | exact RI | (rewrite u_Z2bv by lia; lia)].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - right; right. exists (Z_to_bv 64 rng), 1024%Z. rewrite u_Z2bv by lia. refine (conj Br4 (conj Br5 (conj Br6 (conj _ _)))); lia.
    - left; lia. }
  destruct WP as [W2 PM2].
  assert (PM' : POSTMc C A1 s (pixs + 20) 4 m1 M) by exact (POSTMc_trans _ _ _ _ _ _ _ _ PM (b5_postmc_0 _ _ _ _ _ _ _ _ PM2)).
  assert (AGf : agree_win (s - 320) 320 [] mk M).
  { eapply agree_of_rinv; [exact RI|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; lia. }
  keep_cells CLf AGf CLf'.
  assert (AGb : agree_win bil 104 [] mk M).
  { unfold b5_ap in Db. eapply agree_of_rinv; [exact RI|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; lia. }
  keep_cells CLb AGb CLb'.
  assert (R20' : rdn SEGS M (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { unfold b5_ap in Dp. rewrite (b5_rdn2 mk M rng 1024 (s - 336) 16 (pixs + 20) 4 RI) by b5_zlia. exact R20. }
  assert (NC' : forall j, (0 <= j < 10)%Z -> rdn SEGS M (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { unfold b5_ap in Dn. intros j Hj. rewrite (b5_rdn2 mk M rng 1024 (s - 336) 16 (nc + 4 * j) 4 RI) by b5_zlia. exact (NC j Hj). }
  assert (KX' : kidx_ok kx M)
    by (unfold b5_ap in Dx; exact (b5_arr_keep (fun kv => (0 <= kv <= 8)%Z) mk M rng 1024 (s - 336) 16 kx 256 RI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KX)).
  assert (KF' : kfr_ok kf M)
    by (unfold b5_ap in Df; exact (b5_arr_keep FpSiteB.kfr_le1 mk M rng 1024 (s - 336) 16 kf 256 RI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KF)).
  assert (KS' : kcell_ok spat 11 M)
    by (unfold b5_ap in Ds; exact (b5_arr_keep (FpBound.FB fmt_single 1) mk M rng 1024 (s - 336) 16 spat 11 RI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KS)).
  refine (K fr2 cs2 M r3 FZ2 _ _ _ _ W2 PM' CLf' R20' CLb' NC' KX' KF' KS' KC J2 J8 J9 J18 J19 _ _ _ J23 _ J25 J26 _).
  - rewrite FS2 by b5_infs. exact FI8.
  - rewrite FS2 by b5_infs. rewrite FIK by b5_nrx. exact F9.
  - rewrite FS2 by b5_infs. rewrite FIK by b5_nrx. exact F18.
  - intros r Hr N8 N9 N18. rewrite (FS2 r Hr), (FIK r (b5_fs_K r Hr N8)). exact (FK r Hr N8 N9 N18).
  - rewrite AG2 by b5_nin. rewrite AG1 by b5_nin. exact G20.
  - rewrite AG2 by b5_nin. rewrite AG1 by b5_nin. exact G21.
  - rewrite AG2 by b5_nin. rewrite AG1 by b5_nin. exact G22.
  - rewrite AG2 by b5_nin. rewrite AG1 by b5_nin. exact G24.
  - intros r CS NI. destruct (b5_cs r CS NI) as [-> | [-> | ->]];
      rewrite AG2 by b5_nin; rewrite AG1 by b5_nin; apply GCS; assumption.
Qed.

Lemma bca_11 : forall frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk (s pixs bsc minv maxv bil nc kx kf spat rng : Z) (S : TSet) (g3 : word),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z -> frm_zero csk -> W C Ak mk (with_vmmaps vmk md) -> sub_live A1 Ak -> bc_blk C A1 Ak bil 104 ->
  bc_blk C A1 Ak nc 40 -> bc_blk C A1 Ak kx 1024 -> bc_blk C A1 Ak kf 1024 -> bc_blk C A1 Ak spat 44 -> bc_blk C A1 Ak rng 1024 -> bil <> nc -> bil <> kx -> nc <> kx -> bil <> kf -> nc <> kf ->
  kx <> kf -> bil <> spat -> nc <> spat -> kx <> spat -> kf <> spat -> bil <> rng -> nc <> rng -> kx <> rng -> kf <> rng -> spat <> rng -> (0 <= pixs < 2 ^ 64)%Z ->
  live A1 (Z_to_bv 64 pixs) = Some 64%Z -> POSTMc C A1 s (pixs + 20) 4 m1 mk ->
  cellsAt SEGS mk (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
  rdn SEGS mk (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
  cellsAt SEGS mk bil [(0%Z, 8%nat, pixs); (8%Z, 8%nat, bsc); (16%Z, 4%nat, 1%Z); (48%Z, 4%nat, minv); (52%Z, 4%nat, maxv); (56%Z, 4%nat, 10%Z); (64%Z, 8%nat, nc); (72%Z, 8%nat, kx); (80%Z, 8%nat, kf); (32%Z, 8%nat, spat)] ->
  (forall j, (0 <= j < 10)%Z -> rdn SEGS mk (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx mk -> kfr_ok kf mk -> kcell_ok spat 11 mk -> kcell_ok rng 256 mk ->
  getr rk 2 = Z_to_bv 64 (s - 320) -> getr rk 8 = Z_to_bv 64 256 -> getr rk 9 = Z_to_bv 64 256 -> getr rk 18 = Z_to_bv 64 1 -> getr rk 19 = Z_to_bv 64 1 -> getr rk 20 = Z_to_bv 64 1 ->
  getr rk 21 = Z_to_bv 64 spat -> getr rk 22 = Z_to_bv 64 1 -> getr rk 23 = Z_to_bv 64 rng -> getr rk 24 = Z_to_bv 64 pixs -> getr rk 25 = Z_to_bv 64 (rng + 1024) ->
  getr rk 26 = Z_to_bv 64 (rng + 1024) -> (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr rk r = getr r1 r) -> getr r1 3 = g3 ->
  getr r1 4 = Z_to_bv 64 0x56270 ->
  (forall m' r',
     W C Ak m' (with_vmmaps vmk md) -> POSTMc C A1 s (pixs + 20) 4 m1 m' ->
     cellsAt SEGS m' (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     rdn SEGS m' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) -> cellsAt SEGS m' bil (bc_bl2 pixs bsc minv maxv nc kx kf spat rng) ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) -> kidx_ok kx m' -> kfr_ok kf m' -> kcell_ok spat 11 m' -> kcell_ok rng 256 m' ->
     getr r' 1 = Z_to_bv 64 0x39efc -> getr r' 2 = Z_to_bv 64 (s - 320) -> getr r' 4 = Z_to_bv 64 0x56270 -> getr r' 10 = Z_to_bv 64 10 -> getr r' 8 = Z_to_bv 64 256 -> getr r' 9 = Z_to_bv 64 256 ->
     getr r' 18 = Z_to_bv 64 1 -> getr r' 19 = Z_to_bv 64 1 -> getr r' 20 = Z_to_bv 64 1 -> getr r' 21 = Z_to_bv 64 spat -> getr r' 22 = Z_to_bv 64 1 -> getr r' 23 = Z_to_bv 64 rng ->
     getr r' 24 = Z_to_bv 64 pixs -> getr r' 25 = Z_to_bv 64 (rng + 1024) -> getr r' 26 = Z_to_bv 64 (rng + 1024) -> getr r' 3 = g3 ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r' r = getr r1 r) ->
     realizes SEGS (mkCfg (@mkst (mkFP frk csk) r' (Z_to_bv 64 0x18258) m' al_rom) (with_vmmaps vmk md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP frk csk) rk (Z_to_bv 64 0x39eec) mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros frk csk C A1 m1 md r1 regs0 fr0 Ak mk vmk rk s pixs bsc minv maxv bil nc kx kf spat rng S g3
    CK Hs16 Hstk Htop FZ HW SL Bb Bn Bx Bf Bs Br Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs Nbr Nnr Nxr Nfr Nsr Hpx Lpx PM CS R20 CB NC KI KF KS KR
    H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 HCS H3 H4 K.
  pose proof (b3_apart C A1 Ak mk _ bil nc 104 40 CK HW Bb Bn Nbn eq_refl eq_refl) as Abn.
  pose proof (b3_apart C A1 Ak mk _ bil kx 104 1024 CK HW Bb Bx Nbx eq_refl eq_refl) as Abx.
  pose proof (b3_apart C A1 Ak mk _ bil kf 104 1024 CK HW Bb Bf Nbf eq_refl eq_refl) as Abf.
  pose proof (b3_apart C A1 Ak mk _ bil spat 104 44 CK HW Bb Bs Nbs eq_refl eq_refl) as Abs.
  pose proof (b3_apart C A1 Ak mk _ bil rng 104 1024 CK HW Bb Br Nbr eq_refl eq_refl) as Abr.
  clear Nbn Nbx Nnx Nbf Nnf Nxf Nbs Nns Nxs Nfs Nbr Nnr Nxr Nfr Nsr.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. unfold BC_WIN in Hstk.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof Bb as (Gb & Tb & _ & Lb & Lb1 & Lb0).
  pose proof Bn as (Gn & Tn & _ & Ln & _ & _).
  pose proof Bx as (Gx & Tx & _ & Lx & _ & _).
  pose proof Bf as (Gf & Tf & _ & Lf & _ & _).
  pose proof Bs as (Gs & Ts & _ & Ls & _ & _).
  pose proof Br as (Gr & Tr & _ & Lr & _ & _).
  assert (LpK : live Ak (Z_to_bv 64 pixs) = Some 64%Z) by (apply SL; exact Lpx).
  pose proof (blk_range C Ak mk _ (Z_to_bv 64 pixs) 64 CK HW LpK ltac:(lia)) as BRp. rewrite u_Z2bv in BRp by lia.
  pose proof (b3_cells_r _ _ _ _ CS) as CSt.
  pose proof (b3_cells_l _ _ _ _ CS) as CSf. unfold bc_fl1 in CSf. apply b3_cells_r in CSf.
  assert (C304 : rdn SEGS mk (Z_to_bv 64 (s - 304)) 8 = Some (Z_to_le_bytes 8 bil)) by cell_from CSt.
  assert (C288 : rdn SEGS mk (Z_to_bv 64 (s - 288)) 8 = Some (Z_to_le_bytes 8 10)) by cell_from CSf.
  assert (SOK : store_ok SEGS mk (Z_to_bv 64 (bil + 40)) 8 = true)
    by exact (exW_sok_blk SEGS C Ak mk _ bil 104 (bil + 40) 8 p16_segs CK HW Lb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(b3_zlia)).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) |
    exact (bc_L al_rom (mkFP frk csk) rk mk s bil rng ltac:(lia) Gb ltac:(lia) ltac:(lia) C304 C288 SOK H2 H23 FZ) |].
  intros fin (r' & M' & -> & RI & CR & G1 & G2 & G10 & AG).
  assert (FRS : fresh_regions C Ak A1 [((bil + 40)%Z, 8%Z)]).
  { unfold fresh_regions. apply Forall_cons; [|apply Forall_nil]. exists (Z_to_bv 64 bil), 104%Z. cbn [fst snd]. rewrite u_Z2bv by lia.
    refine (conj Lb (conj Lb1 (conj Lb0 (conj _ _)))); lia. }
  destruct (rinv_WP C A1 Ak mk _ M' _ s CK HW SL Htop RI FRS) as [W' PM'].
  assert (AGs : agree_win (s - 320) 320 [] mk M').
  { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [|apply Forall_nil]. left. cbn [fst snd]. lia. }
  keep_cells CS AGs CS'.
  assert (AGb : agree_win bil 104 [(40%Z, 8%Z)] mk M').
  { eapply agree_of_rinv; [exact RI|]. apply Forall_cons; [|apply Forall_nil]. right. exists (40%Z, 8%Z).
    split; [left; reflexivity|]. cbn [fst snd]. lia. }
  keep_cells CB AGb CB'.
  assert (CB2 : cellsAt SEGS M' bil (bc_bl2 pixs bsc minv maxv nc kx kf spat rng)).
  { unfold bc_bl2. exact (cellsAt_app SEGS M' bil _ _ CB' (cellsAt_cons SEGS M' bil [] 40 8 rng (bil + 40) eq_refl CR (cellsAt_nil SEGS M' bil))). }
  assert (R20' : rdn SEGS M' (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (LIVK_rdn SEGS A1 mk M' (Z_to_bv 64 pixs) 64 (pixs + 20) 4 (proj2 PM') Lpx) by (rewrite u_Z2bv by lia; b3_zlia). exact R20. }
  assert (NC' : forall j, (0 <= j < 10)%Z -> rdn SEGS M' (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))).
  { unfold b3_ap in Abn. intros j Hj. rewrite (b3_rd1 mk M' (bil + 40) 8 (nc + 4 * j) 4 RI) by b3_zlia. exact (NC j Hj). }
  assert (KI' : kidx_ok kx M') by (unfold b3_ap in Abx; apply (b3_kidx_keep kx mk M'); [intros v Hv; apply (b3_rd1 mk M' (bil + 40) 8 _ 4 RI); b3_zlia | exact KI]).
  assert (KF' : kfr_ok kf M') by (unfold b3_ap in Abf; apply (b3_kfr_keep kf mk M'); [intros v Hv; apply (b3_rd1 mk M' (bil + 40) 8 _ 4 RI); b3_zlia | exact KF]).
  assert (KS' : kcell_ok spat 11 M') by (unfold b3_ap in Abs; apply (b3_kcell_keep spat 11 mk M'); [intros v Hv; apply (b3_rd1 mk M' (bil + 40) 8 _ 4 RI); b3_zlia | exact KS]).
  assert (KR' : kcell_ok rng 256 M') by (unfold b3_ap in Abr; apply (b3_kcell_keep rng 256 mk M'); [intros v Hv; apply (b3_rd1 mk M' (bil + 40) 8 _ 4 RI); b3_zlia | exact KR]).
  assert (J3 : getr rk 3 = getr r1 3) by (apply HCS; [exact cs3 | notin_lit]).
  assert (J4 : getr rk 4 = getr r1 4) by (apply HCS; [exact cs4 | notin_lit]).
  refine (K M' r' W' (POSTMc_trans _ _ _ _ _ _ _ _ PM (POSTMc_of_POSTM _ _ _ _ _ _ _ PM')) CS' R20' CB2 NC' KI' KF' KS' KR' G1 G2 _ G10 _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: try (csr; reflexivity).
  intros r CSr NI. rewrite (AG r) by (apply b3_cs_n1_10; exact CSr). apply HCS; assumption.
Qed.


Lemma bc_arrays_W : forall fr cs C A1 m1 md r1 regs0 fr0 (s pixs bsc minv maxv : Z) (S : TSet) (g3 : word),
  Cok C -> W C A1 m1 md -> frm_zero cs -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BC_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr r1 1 = Z_to_bv 64 0x39a18 -> getr r1 2 = Z_to_bv 64 (s - 320) -> getr r1 4 = Z_to_bv 64 0x56270 -> getr r1 10 = Z_to_bv 64 1 -> getr r1 11 = Z_to_bv 64 104 ->
  getr r1 9 = Z_to_bv 64 bsc -> getr r1 22 = Z_to_bv 64 1 -> getr r1 24 = Z_to_bv 64 pixs -> getr r1 3 = g3 ->
  reg_get fr 8 = Z_to_bv 64 0xffffffff41200000 -> reg_get fr 9 = Z_to_bv 64 0xffffffff40a00000 ->
  cellsAt SEGS m1 (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv) -> (0 <= minv <= 255)%Z -> (0 <= maxv <= 255)%Z -> (0 <= bsc < 2 ^ 64)%Z ->
  (0 <= pixs < 2 ^ 64)%Z -> live A1 (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  rdn SEGS m1 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  forall (kR bR : Z), aroom A1 (m_vmmaps md) kR bR -> (6 <= kR)%Z -> (6 * 131072 <= bR)%Z ->
  (forall fr' cs' A7 m7 vm7 r7 (bil nc kx kf spat rng : Z),
     W C A7 m7 (with_vmmaps vm7 md) -> frm_zero cs' -> sub_live A1 A7 -> POSTMc C A1 s (pixs + 20) 4 m1 m7 ->
     rdn SEGS m7 (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 2) ->
     cellsAt SEGS m7 (s - 320) (bc_fl1 regs0 fr0 bsc minv maxv ++ [(16%Z, 8%nat, bil); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)]) ->
     cellsAt SEGS m7 bil (bc_bl2 pixs bsc minv maxv nc kx kf spat rng) ->
     (forall j, (0 <= j < 10)%Z -> rdn SEGS m7 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) ->
     kidx_ok kx m7 -> kfr_ok kf m7 -> kcell_ok spat 11 m7 -> kcell_ok rng 256 m7 ->
     bc_blk C A1 A7 bil 104 -> bc_blk C A1 A7 nc 40 -> bc_blk C A1 A7 kx 1024 -> bc_blk C A1 A7 kf 1024 -> bc_blk C A1 A7 spat 44 -> bc_blk C A1 A7 rng 1024 ->
     (kx <> kf /\ kx <> rng /\ kf <> rng) ->
     (forall q : word, ~ In q (map (Z_to_bv 64) [bil; nc; kx; kf; spat; rng]) -> live A7 q = live A1 q) ->
     getr r7 1 = Z_to_bv 64 0x39efc -> getr r7 2 = Z_to_bv 64 (s - 320) -> getr r7 4 = Z_to_bv 64 0x56270 -> getr r7 10 = Z_to_bv 64 10 ->
     getr r7 8 = Z_to_bv 64 256 -> getr r7 9 = Z_to_bv 64 256 -> getr r7 18 = Z_to_bv 64 1 -> getr r7 19 = Z_to_bv 64 1 -> getr r7 20 = Z_to_bv 64 1 ->
     getr r7 21 = Z_to_bv 64 spat -> getr r7 22 = Z_to_bv 64 1 -> getr r7 23 = Z_to_bv 64 rng -> getr r7 24 = Z_to_bv 64 pixs ->
     getr r7 25 = Z_to_bv 64 (rng + 1024) -> getr r7 26 = Z_to_bv 64 (rng + 1024) -> getr r7 3 = g3 ->
     (forall r : reg, AllocIface.callee_saved r -> ~ In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr r7 r = getr r1 r) ->
     reg_get fr' 8 = Z_to_bv 64 0xffffffff43480000 -> reg_get fr' 9 = Z_to_bv 64 0xffffffff42480000 -> reg_get fr' 18 = Z_to_bv 64 0x4024000000000000 ->
     (forall r : reg, In (u r) fs_list -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r) ->
     aroom A7 vm7 (kR - 6) (bR - 6 * 131072) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r7 (Z_to_bv 64 0x18258) m7 al_rom) (with_vmmaps vm7 md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r1 (Z_to_bv 64 0x3c0f8) m1 al_rom) md) S.
Proof.
  intros until bR. intros AR HkR HbR K.
  apply (bca_1 fr cs C A1 m1 md r1 regs0 fr0 s pixs bsc minv maxv S kR bR); [assumption .. |].
  intros Aq1 mq1 vq1 rq1 bil; intros.
  apply (bca_2 fr cs C A1 m1 md r1 regs0 fr0 Aq1 mq1 vq1 rq1 s pixs bsc minv maxv bil S kR bR); [assumption .. |].
  intros frq2 csq2 Aq2 mq2 vq2 rq2 nc; intros.
  apply (bca_3 frq2 csq2 C A1 m1 md r1 regs0 fr0 Aq2 mq2 vq2 rq2 s pixs bsc minv maxv bil nc S kR bR); [assumption .. |].
  intros Aq3 mq3 vq3 rq3 kx; intros.
  apply (bca_4 fr frq2 csq2 C A1 m1 md r1 regs0 fr0 Aq3 mq3 vq3 rq3 s pixs bsc minv maxv bil nc kx S); [assumption .. |].
  intros frq4 csq4 mq4 rq4; intros.
  apply (bca_5 frq4 csq4 C A1 m1 md r1 regs0 fr0 Aq3 mq4 vq3 rq4 s pixs bsc minv maxv bil nc kx S kR bR); [assumption .. |].
  intros Aq5 mq5 vq5 rq5 kf; intros.
  apply (bca_6 fr frq4 csq4 C A1 m1 md r1 regs0 fr0 Aq5 mq5 vq5 rq5 s pixs bsc minv maxv bil nc kx kf S); [assumption .. |].
  intros frq6 csq6 mq6 rq6; intros.
  apply (bca_7 frq6 csq6 C A1 m1 md r1 regs0 fr0 Aq5 mq6 vq5 rq6 s pixs bsc minv maxv bil nc kx kf S kR bR); [assumption .. |].
  intros Aq7 mq7 vq7 rq7 spat; intros.
  apply (bca_8 fr frq6 csq6 C A1 m1 md r1 regs0 fr0 Aq7 mq7 vq7 rq7 s pixs bsc minv maxv bil nc kx kf spat S); [assumption .. |].
  intros frq8 csq8 mq8 rq8; intros.
  apply (bca_9 frq8 csq8 C A1 m1 md r1 regs0 fr0 Aq7 mq8 vq7 rq8 s pixs bsc minv maxv bil nc kx kf spat S kR bR); [assumption .. |].
  intros Aq9 mq9 vq9 rq9 rng; intros.
  apply (bca_10 fr frq8 csq8 C A1 m1 md r1 regs0 fr0 Aq9 mq9 vq9 rq9 s pixs bsc minv maxv bil nc kx kf spat rng S); [assumption .. |].
  intros frq10 csq10 mq10 rq10; intros.
  apply (bca_11 frq10 csq10 C A1 m1 md r1 regs0 fr0 Aq9 mq10 vq9 rq10 s pixs bsc minv maxv bil nc kx kf spat rng S g3); [assumption .. |].
  intros mq11 rq11; intros.
  apply (K frq10 csq10 Aq9 mq11 vq9 rq11 bil nc kx kf spat rng); try assumption.
  split; [assumption | split; assumption].
Qed.

End BilCW2.
