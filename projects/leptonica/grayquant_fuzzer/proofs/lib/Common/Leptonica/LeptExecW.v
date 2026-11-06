(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptExec.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ExecW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma exW_win : forall C A Ar m md E log (rb : expr) (s F : Z),
  Cok C -> W C A m md -> sub_live Ar A -> log_flat E log ->
  ex_in_regions [(rb, - F, 0)] log = true -> edenot E rb = Z_to_bv 64 s ->
  0 <= F -> c_top C - LSTK <= s - F -> s <= c_top C ->
  W C A (mem_denot E m log) md /\ POSTM C Ar s m (mem_denot E m log).
Proof.
  intros C A Ar m md E log rb s F CK HW SUB Hlf Hreg Hb HF Hlo Hhi.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. pose proof LSTK_val as LV.
  assert (CH : forall a : word, mem_denot E m log a <> m a -> scratch C s a).
  { intros a Hne. pose proof (ex_changed1 E m log rb (- F) 0 s Hlf Hreg Hb ltac:(lia) a Hne) as X. unfold scratch. lia. }
  split.
  - apply (W_local C A m md _ s CK HW Hhi); [intros a Hne; left; exact (CH a Hne) | apply mem_denot_grows].
  - apply (POSTM_local C Ar A m md _ s CK HW SUB). intros a Hne. left. exact (CH a Hne).
Qed.

(* [comment removed for export] *)
Lemma exW_win_blk : forall C A Ar m md E log (rb pb : expr) (s F p n : Z),
  Cok C -> W C A m md -> sub_live Ar A -> log_flat E log ->
  ex_in_regions [(rb, - F, 0); (pb, 0, n)] log = true -> edenot E rb = Z_to_bv 64 s -> edenot E pb = Z_to_bv 64 p ->
  0 <= F -> c_top C - LSTK <= s - F -> s <= c_top C -> 0 <= p < 2 ^ 64 ->
  live A (Z_to_bv 64 p) = Some n -> live Ar (Z_to_bv 64 p) = None -> live (c_A0 C) (Z_to_bv 64 p) = None ->
  W C A (mem_denot E m log) md /\ POSTM C Ar s m (mem_denot E m log).
Proof.
  intros C A Ar m md E log rb pb s F p n CK HW SUB Hlf Hreg Hb Hp HF Hlo Hhi Rp L LR L0.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. pose proof LSTK_val as LV.
  assert (CH : forall a : word, mem_denot E m log a <> m a -> scratch C s a \/ (u (Z_to_bv 64 p) <= u a < u (Z_to_bv 64 p) + n)).
  { intros a Hne. destruct (ex_changed2 E m log rb pb (- F) 0 s 0 n p Hlf Hreg Hb ltac:(lia) Hp Rp a Hne) as [X|X];
      [left; unfold scratch; lia | right; rewrite u_Z2bv by lia; lia]. }
  split.
  - apply (W_local C A m md _ s CK HW Hhi); [|apply mem_denot_grows].
    intros a Hne. destruct (CH a Hne) as [X|X]; [left; exact X | right; exists (Z_to_bv 64 p), n; split; [exact L | split; [exact L0 | exact X]]].
  - apply (POSTM_local C Ar A m md _ s CK HW SUB).
    intros a Hne. destruct (CH a Hne) as [X|X]; [left; exact X | right; exists (Z_to_bv 64 p), n; split; [exact L | split; [exact LR | exact X]]].
Qed.

(* [comment removed for export] *)
Lemma exW_kept_stack : forall C (s' : Z) M M' E (rb : expr) (b lo hi : Z),
  Cok C -> FRM C s' M M' -> c_top C - LSTK <= s' -> edenot E rb = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  s' <= b + lo -> b + hi <= c_top C -> ex_region_kept E M M' (rb, lo, hi).
Proof.
  intros C s' M M' E rb b lo hi CK F Hlo Hb Rb H1 H2. cbn [ex_region_kept]. rewrite Hb, u_Z2bv by lia. intros x Hx.
  destruct CK. laypins. apply F.
  - apply above_not_gap. lia.
  - intros G; apply pin_glob in G; unfold inZ in G; lia.
  - intros G; apply pin_errno in G; unfold inZ in G; lia.
  - unfold hcell; lia.
  - unfold scratch; lia.
Qed.

Lemma exW_kept_blk : forall (A : AS) M M' E (rb : expr) (p n : Z),
  LIVK A M M' -> live A (Z_to_bv 64 p) = Some n -> edenot E rb = Z_to_bv 64 p -> 0 <= p -> p + n < 2 ^ 64 ->
  ex_region_kept E M M' (rb, 0, n).
Proof.
  intros A M M' E rb p n LK L Hb Hp Hn. cbn [ex_region_kept]. rewrite Hb. intros x Hx.
  assert (Hn0 : 0 <= n) by (destruct (Z_le_gt_dec 0 n); [assumption | rewrite u_Z2bv in Hx by lia; lia]).
  rewrite u_Z2bv in Hx by lia.
  replace x with (at_ (Z_to_bv 64 p) (u x - p)).
  - apply (LK (Z_to_bv 64 p) n (u x - p) L). lia.
  - unfold at_. apply bv_eq. rewrite u_Z2bv; rewrite u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma exW_kimg_ro : forall segs C A m md E (lo hi : Z), W C A m md -> fst ll_ro <= lo -> hi <= snd ll_ro -> 0 <= lo -> hi <= 2 ^ 64 ->
  kentry_ok segs E m (KImg lo hi).
Proof.
  intros segs C A m md E lo hi HW H1 H2 H3 H4. apply kimg_intro; [exact H3 | exact H4 |].
  intros i Hi. apply (W_ro C A m md); [exact HW|]. unfold inZ. rewrite u_Z2bv by lia. lia.
Qed.
Lemma exW_kimg_clr : forall segs C A m md E (lo hi clo chi : Z), W C A m md -> In (clo, chi) ll_clr -> clo <= lo -> hi <= chi -> 0 <= lo -> hi <= 2 ^ 64 ->
  kentry_ok segs E m (KImg lo hi).
Proof.
  intros segs C A m md E lo hi clo chi HW Hin H1 H2 H3 H4. apply kimg_intro; [exact H3 | exact H4 |].
  intros i Hi. apply (w_clr _ _ _ _ HW). rewrite u_Z2bv by lia.
  assert (G : forall rs, In (clo, chi) rs -> inZs rs i).
  { induction rs as [|r t IH]; intros Hr; [destruct Hr|]. cbn [inZs]. destruct Hr as [->|Hr]; [left; unfold inZ; cbn [fst snd]; lia | right; exact (IH Hr)]. }
  exact (G _ Hin).
Qed.
End ExecW.

(* [comment removed for export] *)
Lemma exW_ro_None : forall {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout} {PINS : LeptPins} C A m md (lo hi : Z),
  W C A m md -> (fst ll_ro <= lo)%Z -> (hi <= snd ll_ro)%Z -> (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  forall i, (lo <= i < hi)%Z -> m (Z_to_bv 64 i) = None.
Proof. intros AL CL AIC LL PINS C A m md lo hi HW H1 H2 H3 H4 i Hi. apply (W_ro C A m md); [exact HW|]. unfold inZ. rewrite u_Z2bv by lia. lia. Qed.
Lemma exW_clr_None : forall {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout} {PINS : LeptPins} C A m md (lo hi clo chi : Z),
  W C A m md -> In (clo, chi) ll_clr -> (clo <= lo)%Z -> (hi <= chi)%Z -> (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  forall i, (lo <= i < hi)%Z -> m (Z_to_bv 64 i) = None.
Proof.
  intros AL CL AIC LL PINS C A m md lo hi clo chi HW Hin H1 H2 H3 H4 i Hi. apply (w_clr _ _ _ _ HW). rewrite u_Z2bv by lia.
  assert (G : forall rs, In (clo, chi) rs -> inZs rs i).
  { induction rs as [|r t IH]; intros Hr; [destruct Hr|]. cbn [inZs]. destruct Hr as [->|Hr]; [left; unfold inZ; cbn [fst snd]; lia | right; exact (IH Hr)]. }
  exact (G _ Hin).
Qed.
(* [comment removed for export] *)
Ltac exW_cmp := first [ (vm_compute; let X := fresh in intro X; discriminate X) | lia ].
Ltac exW_in := cbn; first [ (left; reflexivity) | (right; left; reflexivity) | (right; right; left; reflexivity)
                          | (right; right; right; left; reflexivity) | (right; right; right; right; left; reflexivity)
                          | (right; right; right; right; right; left; reflexivity) | tauto ].
Ltac exW_ro HW := apply (exW_ro_None _ _ _ _ _ _ HW); cbn; exW_cmp.
Ltac exW_clr HW clo chi := apply (exW_clr_None _ _ _ _ _ _ clo chi HW); [exW_in | exW_cmp | exW_cmp | exW_cmp | exW_cmp].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac exW_cs1 regs0 vals HRc CS r cslem :=
  lazymatch type of HRc with
  | regs_ok ?E ?sr ?Rc =>
    lazymatch type of CS with
    | cs_kept Rc ?r2 =>
        let e := eval vm_compute in (sr_get sr r) in
        lazymatch e with
        | ELit ?z => assert (getr r2 r = Z_to_bv 64 z) by (rewrite (cs_kept_get Rc r2 r CS cslem), (reg_val _ _ _ r HRc); reflexivity)
        | EAlu ALU_ADD (EVar ?i) (ELit ?c) =>
            let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
            lazymatch w with
            | Z_to_bv 64 ?b => assert (getr r2 r = Z_to_bv 64 (b + c)) by (rewrite (cs_kept_get Rc r2 r CS cslem), (reg_val _ _ _ r HRc); change (alu64 ALU_ADD (Z_to_bv 64 b) (Z_to_bv 64 c) = Z_to_bv 64 (b + c)); apply ex_ptr_val)
            | _ => idtac
            end
        | EVar ?i =>
            let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
            lazymatch w with
            | Z_to_bv 64 ?b => assert (getr r2 r = Z_to_bv 64 b) by (rewrite (cs_kept_get Rc r2 r CS cslem), (reg_val _ _ _ r HRc); reflexivity)
            | _ => idtac
            end
        | _ => idtac
        end
    end
  end.
Ltac exW_cs regs0 vals0 HRc CS :=
  let vals := eval hnf in vals0 in
  exW_cs1 regs0 vals HRc CS (2%bv : reg) cs2; exW_cs1 regs0 vals HRc CS (3%bv : reg) cs3; exW_cs1 regs0 vals HRc CS (4%bv : reg) cs4;
  exW_cs1 regs0 vals HRc CS (8%bv : reg) cs8; exW_cs1 regs0 vals HRc CS (9%bv : reg) cs9; exW_cs1 regs0 vals HRc CS (18%bv : reg) cs18;
  exW_cs1 regs0 vals HRc CS (19%bv : reg) cs19; exW_cs1 regs0 vals HRc CS (20%bv : reg) cs20; exW_cs1 regs0 vals HRc CS (21%bv : reg) cs21;
  exW_cs1 regs0 vals HRc CS (22%bv : reg) cs22; exW_cs1 regs0 vals HRc CS (23%bv : reg) cs23; exW_cs1 regs0 vals HRc CS (24%bv : reg) cs24;
  exW_cs1 regs0 vals HRc CS (25%bv : reg) cs25; exW_cs1 regs0 vals HRc CS (26%bv : reg) cs26; exW_cs1 regs0 vals HRc CS (27%bv : reg) cs27.

(* [comment removed for export] *)
Lemma exW_kzero : forall segs E (m : word -> option byte) (e : expr) (p n : Z),
  edenot E e = Z_to_bv 64 p -> (0 <= p)%Z -> (0 < n)%Z -> (p + n <= 2 ^ 64)%Z -> (n < 2 ^ 64)%Z ->
  (forall i, (0 <= i < n)%Z -> m (at_ (Z_to_bv 64 p) i) = Some (Z_to_bv 8 0)) ->
  kentry_ok segs E m (KZero (SA e 0) (ELit n)).
Proof.
  intros segs E m e p n He Hp Hn Hpn Hn64 Hz.
  apply (kzero_intro segs E m e (Z_to_bv 64 p) 0 (ELit n) n He); [cbn [edenot]; apply u_Z2bv; lia | rewrite u_Z2bv by lia; lia | exact Hn | rewrite u_Z2bv by lia; lia |].
  intros i Hi. rewrite u_Z2bv by lia. rewrite Z.add_0_r. specialize (Hz i Hi). unfold at_ in Hz. rewrite u_Z2bv in Hz by lia. exact Hz.
Qed.

(* [comment removed for export] *)
Section ExecW2.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Lemma exW_blk_img_apart : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 < n)%Z -> (0 <= p)%Z -> (p + n < 2 ^ 64)%Z ->
  (fst ll_img < snd ll_img)%Z -> (p + n <= fst ll_img \/ snd ll_img <= p)%Z.
Proof.
  intros C A m md p n CK HW L Hn Hp Hpn Himg.
  destruct (Z_le_gt_dec (p + n) (fst ll_img)) as [X|X]; [left; exact X|]. destruct (Z_le_gt_dec (snd ll_img) p) as [Y|Y]; [right; exact Y|]. exfalso.
  pose proof pin_img64 as (I0 & I1).
  (* [comment removed for export] *)
  assert (Ha : (0 <= Z.max p (fst ll_img) < 2 ^ 64)%Z) by (destruct I0 as [I00 I01]; change (2 ^ 40)%Z with 1099511627776%Z in I1; change (2 ^ 64)%Z with 18446744073709551616%Z in *; lia).
  destruct (blk_byte C A m md (Z_to_bv 64 p) n (Z_to_bv 64 (Z.max p (fst ll_img))) CK HW L ltac:(rewrite !u_Z2bv by lia; lia)) as (_ & _ & NI & _).
  apply NI. unfold inZ. rewrite u_Z2bv by lia. lia.
Qed.
End ExecW2.

(* [comment removed for export] *)
Section ExecW3.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Lemma exW_kwr_blk : forall segs C A m md E (e : expr) (p n : Z), al_segs = segs -> Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some n -> edenot E e = Z_to_bv 64 p -> (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (0 < n)%Z ->
  kentry_ok segs E m (KWr (SA e 0) n).
Proof.
  intros segs C A m md E e p n Hsegs CK HW L He Hp Hpn Hn. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite He, u_Z2bv by lia.
  split; [lia|]. intros d k Hd Hk. destruct k as [|k]; [reflexivity|]. rewrite <- Hsegs.
  apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:Ex; [discriminate|]. exfalso.
  destruct (blk_byte C A m md (Z_to_bv 64 p) n x CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D Ex).
Qed.
End ExecW3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExecW4.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition exW_blk_ok (C : lctx) (A Ar : AS) (E : env) (b : expr * Z * Z) : Prop :=
  match b with (pb, p, n) =>
    edenot E pb = Z_to_bv 64 p /\ (0 <= p < 2 ^ 64)%Z /\ live A (Z_to_bv 64 p) = Some n /\ live Ar (Z_to_bv 64 p) = None /\ live (c_A0 C) (Z_to_bv 64 p) = None end.
Definition exW_blk_region (b : expr * Z * Z) : expr * Z * Z := match b with (pb, _, n) => (pb, 0%Z, n) end.

Lemma exW_win_blks : forall C A Ar m md E log (rb : expr) (s F : Z) (blks : list (expr * Z * Z)),
  Cok C -> W C A m md -> sub_live Ar A -> log_flat E log ->
  ex_in_regions ((rb, (- F)%Z, 0%Z) :: map exW_blk_region blks) log = true -> edenot E rb = Z_to_bv 64 s ->
  (0 <= F)%Z -> (c_top C - LSTK <= s - F)%Z -> (s <= c_top C)%Z -> Forall (exW_blk_ok C A Ar E) blks ->
  W C A (mem_denot E m log) md /\ POSTM C Ar s m (mem_denot E m log).
Proof.
  intros C A Ar m md E log rb s F blks CK HW SUB Hlf Hreg Hb HF Hlo Hhi HB.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. pose proof LSTK_val as LV.
  assert (CH : forall a : word, mem_denot E m log a <> m a ->
             scratch C s a \/ (exists p n, live A p = Some n /\ live Ar p = None /\ live (c_A0 C) p = None /\ (u p <= u a < u p + n)%Z)).
  { intros a Hne. pose proof (ex_changed E m log _ Hlf Hreg a Hne) as X.
    inversion X as [r l H|r l H]; subst.
    - left. rewrite Hb, u_Z2bv in H by lia. unfold scratch. lia.
    - right. apply Exists_exists in H. destruct H as (r & Hin & Hr). apply in_map_iff in Hin. destruct Hin as ([[pb p] n] & <- & Hin).
      rewrite Forall_forall in HB. destruct (HB _ Hin) as (He & Rp & L & LR & L0). cbn [exW_blk_region] in Hr. rewrite He, u_Z2bv in Hr by lia.
      exists (Z_to_bv 64 p), n. rewrite u_Z2bv by lia. repeat split; try assumption; lia. }
  split.
  - apply (W_local C A m md _ s CK HW Hhi); [|apply mem_denot_grows].
    intros a Hne. destruct (CH a Hne) as [X|(p & n & L & LR & L0 & R)]; [left; exact X | right; exists p, n; split; [exact L | split; [exact L0 | exact R]]].
  - apply (POSTM_local C Ar A m md _ s CK HW SUB).
    intros a Hne. destruct (CH a Hne) as [X|(p & n & L & LR & L0 & R)]; [left; exact X | right; exists p, n; split; [exact L | split; [exact LR | exact R]]].
Qed.

(* [comment removed for export] *)
Lemma exW_blk_apart : forall C A m md (p q n k : Z), Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some n -> live A (Z_to_bv 64 q) = Some k -> p <> q -> (0 <= p < 2 ^ 64)%Z -> (0 <= q < 2 ^ 64)%Z -> (0 <= n)%Z -> (0 <= k)%Z ->
  (p + n <= q \/ q + k <= p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Rp Rq Hn Hk.
  assert (NE' : Z_to_bv 64 p <> Z_to_bv 64 q) by (intros X; apply NE; apply (f_equal bv_unsigned) in X; rewrite !u_Z2bv in X by lia; exact X).
  destruct (ai_live_disjoint A m (m_vmmaps md) _ n _ k (w_inv _ _ _ _ HW) Lp Lq NE') as [X|X]; rewrite !u_Z2bv in X by lia;
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

(* [comment removed for export] *)
Lemma exW_blk_apart_h : forall C A m md (p q n k : Z), Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some n -> live A (Z_to_bv 64 q) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 q -> (0 <= p < 2 ^ 64)%Z -> (0 <= q < 2 ^ 64)%Z -> (0 <= n)%Z -> (0 <= k)%Z ->
  ex_apart (p + 0) n (q + 0) k.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Rp Rq Hn Hk. unfold ex_apart. rewrite !Z.add_0_r.
  apply (exW_blk_apart C A m md p q n k CK HW Lp Lq); try assumption. intros ->. apply NE. reflexivity.
Qed.
Lemma exW_blk_img_apart_h : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 < n)%Z -> (0 <= p)%Z -> (p + n < 2 ^ 64)%Z ->
  (fst ll_img < snd ll_img)%Z -> ex_apart (0 + fst ll_img) (snd ll_img - fst ll_img) (p + 0) n.
Proof.
  intros C A m md p n CK HW L Hn Hp Hpn Himg. unfold ex_apart. rewrite Z.add_0_r, Z.add_0_l.
  destruct (exW_blk_img_apart C A m md p n CK HW L Hn Hp Hpn Himg) as [X|X]; [right; exact X | left; lia].
Qed.
(* [comment removed for export] *)
Lemma exW_win_blk_apart_h : forall C A m md (s F p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 < n)%Z -> (0 <= p < 2 ^ 64)%Z ->
  (c_top C - LSTK <= s - F)%Z -> ex_apart (s + - F) F (p + 0) n.
Proof.
  intros C A m md s F p n CK HW L Hn Rp Hlo. unfold ex_apart. right.
  destruct (blk_range C A m md (Z_to_bv 64 p) n CK HW L Hn) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  destruct CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val. lia.
Qed.
End ExecW4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exW_cs_idx : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition exW_sr_call (sr srJ : list expr) : list expr :=
  map (fun k => if existsb (Nat.eqb k) exW_cs_idx then nth k sr (ELit 0) else nth k srJ (ELit 0)) (seq 0 32).

Lemma exW_cs_idx_ok : forall r : reg, existsb (Nat.eqb (ridx r)) exW_cs_idx = true -> callee_saved r.
Proof.
  intros r H. apply existsb_exists in H. destruct H as (k & Hin & Hk). apply Nat.eqb_eq in Hk. subst k. unfold callee_saved.
  pose proof (bv_unsigned_in_range _ r) as Rr. unfold ridx in Hin. cbn [exW_cs_idx In] in Hin.
  assert (E : forall z : Z, Z.to_nat (bv_unsigned r) = Z.to_nat z -> (0 <= z)%Z -> bv_unsigned r = z) by (intros z Hz Hz0; lia).
  destruct Hin as [H|[H|[H|[H|[H|H]]]]].
  - left. apply bv_eq. symmetry in H. apply (E 2%Z) in H; [exact H | lia].
  - right; left. apply bv_eq. symmetry in H. apply (E 3%Z) in H; [exact H | lia].
  - right; right; left. apply bv_eq. symmetry in H. apply (E 4%Z) in H; [exact H | lia].
  - right; right; right; left. apply bv_eq. symmetry in H. apply (E 8%Z) in H; [exact H | lia].
  - right; right; right; right; left. apply bv_eq. symmetry in H. apply (E 9%Z) in H; [exact H | lia].
  - right; right; right; right; right. repeat (destruct H as [H|H]; [lia|]). destruct H.
Qed.

Lemma exW_regs_call : forall (E : env) (sr srJ : list expr) (Rc regs' : bvmap 5 word),
  regs_ok E sr Rc -> regs_ok E srJ regs' -> cs_kept Rc regs' -> regs_ok E (exW_sr_call sr srJ) regs'.
Proof.
  intros E sr srJ Rc regs' HR HJ CS r. pose proof (HJ r) as HJr. pose proof (HR r) as HRr. unfold sr_get in *.
  destruct (bv_eqb r 0) eqn:Hr0; [exact HJr|].
  pose proof (ridx_range r) as Hlt. unfold exW_sr_call.
  rewrite (nth_indep _ (ELit 0) ((fun k => if existsb (Nat.eqb k) exW_cs_idx then nth k sr (ELit 0) else nth k srJ (ELit 0)) 0%nat))
    by (rewrite length_map, length_seq; exact Hlt).
  rewrite (map_nth (fun k => if existsb (Nat.eqb k) exW_cs_idx then nth k sr (ELit 0) else nth k srJ (ELit 0)) (seq 0 32) 0%nat (ridx r)).
  rewrite seq_nth by exact Hlt. cbn [Nat.add].
  destruct (existsb (Nat.eqb (ridx r)) exW_cs_idx) eqn:Hc; [| exact HJr].
  rewrite (CS r (exW_cs_idx_ok r Hc)). exact HRr.
Qed.

(* [comment removed for export] *)
Ltac exW_regfact regs0 vals0 HRc r name :=
  let vals := eval hnf in vals0 in
  lazymatch type of HRc with
  | regs_ok ?E ?sr ?Rc =>
      let e := eval vm_compute in (sr_get sr r) in
      lazymatch e with
      | ELit ?z => assert (name : getr Rc r = Z_to_bv 64 z) by (rewrite (reg_val _ _ _ r HRc); reflexivity)
      | EAlu ALU_ADD (EVar ?i) (ELit ?c) =>
          let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
          lazymatch w with Z_to_bv 64 ?b => assert (name : getr Rc r = Z_to_bv 64 (b + c)) by (rewrite (reg_val _ _ _ r HRc); change (alu64 ALU_ADD (Z_to_bv 64 b) (Z_to_bv 64 c) = Z_to_bv 64 (b + c)); apply ex_ptr_val) end
      | EVar ?i =>
          let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
          lazymatch w with Z_to_bv 64 ?b => assert (name : getr Rc r = Z_to_bv 64 b) by (rewrite (reg_val _ _ _ r HRc); reflexivity) end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exW_sx32 : forall z : Z, (0 <= z < 2 ^ 31)%Z -> ext_val true 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. apply ext_val_sx_id; [lia|]. rewrite u_Z2bv by lia. change (8 * Z.of_nat 4 - 1)%Z with 31%Z. lia. Qed.

(* [comment removed for export] *)
Fixpoint exW_small (e : expr) : option nat :=
  match e with EVar i => Some i | EExt _ O 4 e' => exW_small e' | _ => None end.
Lemma exW_small_sound : forall E (e : expr) (i : nat) (z : Z), exW_small e = Some i -> ev E i = Z_to_bv 64 z -> (0 <= z < 2 ^ 31)%Z ->
  edenot E e = Z_to_bv 64 z.
Proof.
  intros E e. induction e as [x|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n e' IH|sx k j n]; intros i z H Hv Hz;
    cbn [exW_small] in H; try discriminate H.
  - injection H as <-. exact Hv.
  - destruct lo as [|lo]; [|discriminate H]. do 4 (destruct n as [|n]; [discriminate H|]). destruct n as [|n]; [|discriminate H].
    cbn [edenot]. rewrite (IH i z H Hv Hz). destruct sx; [apply exW_sx32; exact Hz|].
    apply ext_val_zx_id. rewrite u_Z2bv by lia. change (8 * Z.of_nat 4)%Z with 32%Z. lia.
Qed.

Ltac exW_regfactX regs0 vals0 HRc r name :=
  let vals := eval hnf in vals0 in
  lazymatch type of HRc with
  | regs_ok ?E ?sr ?Rc =>
      let e := eval vm_compute in (sr_get sr r) in
      lazymatch e with
      | EExt _ _ _ _ =>
          let o := eval vm_compute in (exW_small e) in
          lazymatch o with
          | Some ?i =>
              let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
              lazymatch w with Z_to_bv 64 ?b =>
                assert (name : getr Rc r = Z_to_bv 64 b)
                  by (rewrite (reg_val _ _ _ r HRc); apply (exW_small_sound E e i b); [vm_cast_no_check (eq_refl o) | reflexivity | lia]) end
          end
      | _ => exW_regfact regs0 vals0 HRc r name
      end
  end.

Ltac exW_adenot b rk := unfold adenot; cbn [a_base a_off]; change (v_addi (Z_to_bv 64 b) rk = Z_to_bv 64 (b + rk)); apply zbv_addi.
Ltac exW_scs0 := first [ exact I | (split_scs; fail) ].
Ltac exW_cell HK Hlf vals0 rb b rk n name :=
  let vals := eval hnf in vals0 in
  lazymatch type of HK with
  | know_ok ?segs ?E ?m ?kn =>
    lazymatch type of Hlf with
    | log_flat _ ?log =>
      let lk := eval vm_compute in (ex_lookup segs kn log rb rk n) in
      lazymatch lk with
      | Some (?v, ?scs) =>
          let scs0 := eval vm_compute in (flat_sc kn (SA rb rk) n ++ scs) in
          let tacZ z pf :=
            pose proof (ex_cell_Z segs E m kn log rb rk n v scs scs0 (b + rk)%Z z HK Hlf ltac:(lia) ltac:(lia)
                          ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exW_scs0)
                          ltac:(exW_adenot b rk) ltac:(pf) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia)) as name in
          lazymatch v with
          | ELit ?z => tacZ z ltac:(reflexivity)
          | EVar ?i =>
              let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
              lazymatch w with
              | Z_to_bv 64 ?z => tacZ z ltac:(reflexivity)
              | _ => pose proof (ex_cell_w segs E m kn log rb rk v scs scs0 (b + rk)%Z w HK Hlf
                                   ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exW_scs0)
                                   ltac:(exW_adenot b rk) ltac:(reflexivity)) as name
              end
          | EAlu ALU_ADD (EVar ?i) (ELit ?c) =>
              let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
              lazymatch w with Z_to_bv 64 ?z0 => tacZ (z0 + c)%Z ltac:(change (alu64 ALU_ADD (Z_to_bv 64 z0) (Z_to_bv 64 c) = Z_to_bv 64 (z0 + c)); apply ex_ptr_val) end
          | EExt _ _ _ _ =>
              let o := eval vm_compute in (exW_small v) in
              lazymatch o with
              | Some ?i =>
                  let w := eval cbv beta iota delta [nth] in (nth i vals (Z_to_bv 64 0)) in
                  lazymatch w with Z_to_bv 64 ?z0 => tacZ z0 ltac:(apply (exW_small_sound E v i z0); [vm_cast_no_check (eq_refl o) | reflexivity | lia]) end
              end
          | _ => fail 100 "exW_cell: value form not supported:" v
          end
      | _ => fail 100 "exW_cell: no value at" rb rk
      end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExecW5.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma exW_sok_blk : forall segs C A m md (p n a : Z) (k : nat), al_segs = segs -> Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some n -> (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> (p <= a)%Z -> (a + Z.of_nat k <= p + n)%Z ->
  store_ok segs m (Z_to_bv 64 a) k = true.
Proof.
  intros segs C A m md p n a k Hsegs CK HW L Hp Hpn Ha Hk. destruct k as [|k]; [reflexivity|]. rewrite <- Hsegs.
  apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:Ex; [discriminate|]. exfalso.
  destruct (blk_byte C A m md (Z_to_bv 64 p) n x CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D Ex).
Qed.

Lemma exW_framed : forall C A Ar m md m' (s p n lo hi : Z), Cok C -> W C A m md -> sub_live Ar A -> (s <= c_top C)%Z ->
  mem_grows m m' -> (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) ->
  live A (Z_to_bv 64 p) = Some n -> live Ar (Z_to_bv 64 p) = None -> live (c_A0 C) (Z_to_bv 64 p) = None ->
  (0 <= p < 2 ^ 64)%Z -> (p <= lo)%Z -> (hi <= p + n)%Z ->
  W C A m' md /\ POSTM C Ar s m m'.
Proof.
  intros C A Ar m md m' s p n lo hi CK HW SUB Hs GR FRM L LR L0 Rp Hlo Hhi.
  assert (CH : forall a : word, m' a <> m a -> (u (Z_to_bv 64 p) <= u a < u (Z_to_bv 64 p) + n)%Z).
  { intros a NE. rewrite u_Z2bv by lia. destruct (Z_le_gt_dec lo (u a)) as [X|X]; [destruct (Z_lt_ge_dec (u a) hi) as [Y|Y]; [lia|] |];
      exfalso; apply NE; apply FRM; lia. }
  split.
  - apply (W_local C A m md m' s CK HW Hs); [|exact GR]. intros a NE. right. exists (Z_to_bv 64 p), n. split; [exact L | split; [exact L0 | exact (CH a NE)]].
  - apply (POSTM_local C Ar A m md m' s CK HW SUB). intros a NE. right. exists (Z_to_bv 64 p), n. split; [exact L | split; [exact LR | exact (CH a NE)]].
Qed.
End ExecW5.

(* [comment removed for export] *)
Lemma exW_kept_frame : forall E (M M' : word -> option byte) (rb : expr) (b rlo rlen q qn lo hi : Z),
  (forall x : word, ~ (lo <= bv_unsigned x < hi)%Z -> M' x = M x) -> edenot E rb = Z_to_bv 64 b -> (0 <= b < 2 ^ 64)%Z ->
  ex_apart (b + rlo) rlen (q + 0) qn -> (q <= lo)%Z -> (hi <= q + qn)%Z ->
  ex_region_kept E M M' (rb, rlo, (rlo + rlen)%Z).
Proof.
  intros E M M' rb b rlo rlen q qn lo hi FRM He Rb AP Hlo Hhi. cbn [ex_region_kept]. rewrite He, u_Z2bv by lia. intros x Hx.
  apply FRM. unfold ex_apart in AP. lia.
Qed.

(* [comment removed for export] *)
Definition exW_sr_keep (L : list nat) (sr srJ : list expr) : list expr :=
  map (fun k => if existsb (Nat.eqb k) L then nth k srJ (ELit 0) else nth k sr (ELit 0)) (seq 0 32).
Lemma exW_regs_keep : forall (E : env) (sr srJ : list expr) (Rc regs' : bvmap 5 word) (L : list nat),
  regs_ok E sr Rc -> regs_ok E srJ regs' -> (forall r : reg, existsb (Nat.eqb (ridx r)) L = false -> getr regs' r = getr Rc r) ->
  regs_ok E (exW_sr_keep L sr srJ) regs'.
Proof.
  intros E sr srJ Rc regs' L HR HJ AG r. pose proof (HJ r) as HJr. pose proof (HR r) as HRr. unfold sr_get in *.
  destruct (bv_eqb r 0) eqn:Hr0; [exact HJr|].
  pose proof (ridx_range r) as Hlt. unfold exW_sr_keep.
  rewrite (nth_indep _ (ELit 0) ((fun k => if existsb (Nat.eqb k) L then nth k srJ (ELit 0) else nth k sr (ELit 0)) 0%nat))
    by (rewrite length_map, length_seq; exact Hlt).
  rewrite (map_nth (fun k => if existsb (Nat.eqb k) L then nth k srJ (ELit 0) else nth k sr (ELit 0)) (seq 0 32) 0%nat (ridx r)).
  rewrite seq_nth by exact Hlt. cbn [Nat.add].
  destruct (existsb (Nat.eqb (ridx r)) L) eqn:Hc; [exact HJr|]. rewrite (AG r Hc). exact HRr.
Qed.
(* [comment removed for export] *)
Lemma exW_agree_keep : forall (Rc regs' : bvmap 5 word) (l : list reg),
  regs_agree (fun r => In r l) Rc regs' -> forall r : reg, existsb (Nat.eqb (ridx r)) (map ridx l) = false -> getr regs' r = getr Rc r.
Proof.
  intros Rc regs' l AG r H. apply AG. intros Hin. assert (X : existsb (Nat.eqb (ridx r)) (map ridx l) = true); [|rewrite X in H; discriminate H].
  apply existsb_exists. exists (ridx r). split; [apply in_map; exact Hin | apply Nat.eqb_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExecW6.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
Context {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma exW_blk_rng : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (0 < n)%Z ->
  (4096 <= p)%Z /\ (p + n <= alloc_top (c_vm C))%Z /\ (p + n < 2 ^ 47)%Z.
Proof.
  intros C A m md p n CK HW L Rp Hn. destruct (blk_range C A m md (Z_to_bv 64 p) n CK HW L Hn) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  destruct CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val. lia.
Qed.

Lemma exW_kn_blk : forall segs C A m md E (e we : expr) (p n s F ilo ilen : Z),
  al_segs = segs -> Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (0 < n)%Z ->
  edenot E e = Z_to_bv 64 p -> edenot E we = Z_to_bv 64 s -> (0 <= s < 2 ^ 64)%Z -> (p mod 16 = 0)%Z ->
  (forall i, (0 <= i < n)%Z -> m (at_ (Z_to_bv 64 p) i) = Some (Z_to_bv 8 0)) ->
  ex_apart (s + - F) F (p + 0) n -> ex_apart (0 + ilo) ilen (p + 0) n ->
  Forall (kentry_ok segs E m) [KRange e 4096 (2 ^ 47); KAlign e 16; KZero (SA e 0) (ELit n); KDisj (SA we (- F)) F (SA e 0) n;
                               KDisj (SA (ELit 0) ilo) ilen (SA e 0) n; KWr (SA e 0) n].
Proof.
  intros segs C A m md E e we p n s F ilo ilen Hsegs CK HW L Rp Hn He Hwe Rs Hal HZ AP1 AP2.
  destruct (exW_blk_rng C A m md p n CK HW L Rp Hn) as (G1 & G2 & G3).
  repeat apply Forall_cons; [ | | | | | | apply Forall_nil].
  - apply (ex_krange segs E m e p 4096 (2 ^ 47) He Rp). lia.
  - apply (ex_kalign segs E m e p 16 He Rp); [lia | exact Hal].
  - apply (exW_kzero segs E m e p n He); [lia | lia | lia | lia | exact HZ].
  - exact (ex_kdisj_apart segs E m we e s p (- F) F 0 n Hwe He Rs Rp AP1).
  - exact (ex_kdisj_apart segs E m (ELit 0) e 0 p ilo ilen 0 n eq_refl He ltac:(lia) Rp AP2).
  - apply (exW_kwr_blk segs C A m md E e p n Hsegs CK HW L He); lia.
Qed.

Lemma exW_kn_fixed : forall segs C A m md E (cve we : expr) (cv s F can rolo rohi glo ghi clo chi : Z),
  W C A m md ->
  edenot E cve = Z_to_bv 64 cv -> (0 <= cv < 2 ^ 64)%Z -> rdn segs m (Z_to_bv 64 can) 8 = Some (Z_to_le_bytes 8 cv) ->
  (0 <=? can)%Z = true -> (can + 8 <=? 2 ^ 64)%Z = true ->
  edenot E we = Z_to_bv 64 s -> store_ok segs m (Z_to_bv 64 (s - F)) (Z.to_nat F) = true -> (0 <? F)%Z = true -> (F <= s)%Z -> (s < 2 ^ 64)%Z ->
  (fst ll_ro <=? rolo)%Z = true -> (rohi <=? snd ll_ro)%Z = true -> (0 <=? rolo)%Z = true -> (rohi <=? 2 ^ 64)%Z = true ->
  In (clo, chi) ll_clr -> (clo <=? glo)%Z = true -> (ghi <=? chi)%Z = true -> (0 <=? glo)%Z = true -> (ghi <=? 2 ^ 64)%Z = true ->
  Forall (kentry_ok segs E m) [KWord (SA (ELit 0) can) 8 cve; KWr (SA we (- F)) F; KImg rolo rohi; KImg glo ghi].
Proof.
  intros segs C A m md E cve we cv s F can rolo rohi glo ghi clo chi HW Hcve Rcv Hcan C1 C2 Hwe SOK F0 Fs S64 R1 R2 R3 R4 Hin G1 G2 G3 G4.
  apply Z.leb_le in C1, C2, R1, R2, R3, R4, G1, G2, G3, G4. apply Z.ltb_lt in F0.
  repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - apply (ex_kword_Z segs E m (ELit 0) cve 0 can cv 8 eq_refl Hcve); try lia. exact Hcan.
  - apply (ex_kwr segs E m we s (- F) F (s - F) (Z.to_nat F) Hwe SOK); rewrite ?Z2Nat.id by lia; lia.
  - exact (exW_kimg_ro segs C A m md E rolo rohi HW R1 R2 R3 R4).
  - exact (exW_kimg_clr segs C A m md E glo ghi clo chi HW Hin G1 G2 G3 G4).
Qed.

Lemma exW_kwr_blk2 : forall segs C A m md E (e : expr) (p n : Z), al_segs = segs -> Cok C -> W C A m md ->
  live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (0 <? n)%Z = true -> edenot E e = Z_to_bv 64 p ->
  Forall (kentry_ok segs E m) [KWr (SA e 0) n].
Proof.
  intros segs C A m md E e p n Hsegs CK HW L Rp Hn He. apply Z.ltb_lt in Hn.
  destruct (exW_blk_rng C A m md p n CK HW L Rp Hn) as (G1 & G2 & G3).
  apply Forall_cons; [|apply Forall_nil]. apply (exW_kwr_blk segs C A m md E e p n Hsegs CK HW L He); lia.
Qed.

Lemma exW_blk_img_apart_h2 : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (0 <? n)%Z = true ->
  (fst ll_img <? snd ll_img)%Z = true -> ex_apart (0 + fst ll_img) (snd ll_img - fst ll_img) (p + 0) n.
Proof.
  intros C A m md p n CK HW L Rp Hn Hi. apply Z.ltb_lt in Hn, Hi. destruct (exW_blk_rng C A m md p n CK HW L Rp Hn) as (G1 & G2 & G3).
  apply (exW_blk_img_apart_h C A m md p n CK HW L Hn); lia.
Qed.

Lemma exW_kn_clr : forall segs C A m md E (lo hi clo chi : Z), W C A m md -> In (clo, chi) ll_clr ->
  (clo <=? lo)%Z = true -> (hi <=? chi)%Z = true -> (0 <=? lo)%Z = true -> (hi <=? 2 ^ 64)%Z = true ->
  Forall (kentry_ok segs E m) [KImg lo hi].
Proof.
  intros segs C A m md E lo hi clo chi HW Hin G1 G2 G3 G4. apply Z.leb_le in G1, G2, G3, G4.
  apply Forall_cons; [|apply Forall_nil]. exact (exW_kimg_clr segs C A m md E lo hi clo chi HW Hin G1 G2 G3 G4).
Qed.

Lemma exW_kept_blk2 : forall C (A Aw : AS) (mw : word -> option byte) mdw M M' E (rb : expr) (p n : Z),
  Cok C -> W C Aw mw mdw -> live Aw (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (0 <? n)%Z = true ->
  LIVK A M M' -> live A (Z_to_bv 64 p) = Some n -> edenot E rb = Z_to_bv 64 p ->
  ex_region_kept E M M' (rb, 0%Z, n).
Proof.
  intros C A Aw mw mdw M M' E rb p n CK HW Lw Rp Hn LK L He. apply Z.ltb_lt in Hn.
  destruct (exW_blk_rng C Aw mw mdw p n CK HW Lw Rp Hn) as (G1 & G2 & G3).
  apply (exW_kept_blk A M M' E rb p n LK L He); lia.
Qed.

Lemma exW_kept_stack2 : forall C (s off F : Z) M M' E (rb : expr),
  Cok C -> FRM C (s + off) M M' -> (c_top C - LSTK + F <= s)%Z -> (s <= c_top C)%Z -> (- F <=? off)%Z = true -> (off <=? 0)%Z = true ->
  edenot E rb = Z_to_bv 64 s -> ex_region_kept E M M' (rb, off, 0%Z).
Proof.
  intros C s off F M M' E rb CK FR Hlo Hhi O1 O2 He. apply Z.leb_le in O1, O2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof LSTK_val as LV. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  apply (exW_kept_stack C (s + off) M M' E rb s off 0 CK FR); [lia | exact He | lia | lia | lia].
Qed.
End ExecW6.

(* [comment removed for export] *)
Definition exW_canary (segs : list Segment) (a : Z) (m : word -> option byte) : Z :=
  match rdn segs m (Z_to_bv 64 a) 8 with Some bs => bytes_le_to_Z bs | None => 0%Z end.
Lemma exW_canary_ok : forall segs a m, (exists cv, (0 <= cv < 2 ^ 64)%Z /\ rdn segs m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 cv)) ->
  (0 <= exW_canary segs a m < 2 ^ 64)%Z /\ rdn segs m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 (exW_canary segs a m)).
Proof.
  intros segs a m (cv & Rcv & H). unfold exW_canary. rewrite H.
  assert (E : bytes_le_to_Z (Z_to_le_bytes 8 cv) = cv).
  { rewrite (LeptStructs.lez_u 8 cv ltac:(lia)); [apply u_Z2bv; lia|]. change (8 * Z.of_nat 8)%Z with 64%Z. lia. }
  rewrite E. split; [exact Rcv | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac exW_assoc bs i :=
  lazymatch bs with
  | (?j, ?z) :: ?t => lazymatch j with i => z | _ => exW_assoc t i end
  | _ => fail 100 "exW_assoc: no base for variable" i
  end.
Ltac exW_regfactB bs0 HRc r name :=
  let bs := eval hnf in bs0 in
  lazymatch type of HRc with
  | regs_ok ?E ?sr ?Rc =>
      let e := eval vm_compute in (sr_get sr r) in
      lazymatch e with
      | ELit ?z => assert (name : getr Rc r = Z_to_bv 64 z) by (exact (reg_val _ _ _ r HRc))
      | EAlu ALU_ADD (EVar ?i) (ELit ?c) =>
          let b := exW_assoc bs i in
          assert (name : getr Rc r = Z_to_bv 64 (b + c)) by (exact (eq_trans (reg_val _ _ _ r HRc) (ex_ptr_val b c)))
      | EVar ?i =>
          let b := exW_assoc bs i in
          assert (name : getr Rc r = Z_to_bv 64 b) by (exact (reg_val _ _ _ r HRc))
      | EExt _ _ _ _ =>
          let o := eval vm_compute in (exW_small e) in
          lazymatch o with
          | Some ?i =>
              let b := exW_assoc bs i in
              assert (name : getr Rc r = Z_to_bv 64 b)
                by (refine (eq_trans (reg_val _ _ _ r HRc) _); apply (exW_small_sound E e i b); [vm_cast_no_check (eq_refl o) | reflexivity | lia])
          end
      end
  end.

(* [comment removed for export] *)
Ltac exW_cellB HK Hlf r0 bs0 rb b rk n name :=
  let bs := eval hnf in bs0 in
  lazymatch type of HK with
  | know_ok ?segs ?E ?m ?kn =>
    lazymatch type of Hlf with
    | log_flat _ ?log =>
      let lk := eval vm_compute in (ex_lookup segs kn log rb rk n) in
      lazymatch lk with
      | Some (?v, ?scs) =>
          let scs0 := eval vm_compute in (flat_sc kn (SA rb rk) n ++ scs) in
          let tacZ z pf :=
            pose proof (ex_cell_Z segs E m kn log rb rk n v scs scs0 (b + rk)%Z z HK Hlf ltac:(lia) ltac:(lia)
                          ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exW_scs0)
                          ltac:(exW_adenot b rk) ltac:(pf) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia)) as name in
          lazymatch v with
          | ELit ?z => tacZ z ltac:(reflexivity)
          | EVar ?i =>
              let small := eval vm_compute in (Nat.ltb i 32) in
              lazymatch small with
              | true =>
                  let rg := eval cbv beta iota delta [nth ex_regs_list] in (nth i ex_regs_list ex_r1) in
                  pose proof (ex_cell_w segs E m kn log rb rk v scs scs0 (b + rk)%Z (getr r0 rg) HK Hlf
                                ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exW_scs0)
                                ltac:(exW_adenot b rk) ltac:(reflexivity)) as name
              | false => let z := exW_assoc bs i in tacZ z ltac:(reflexivity)
              end
          | EAlu ALU_ADD (EVar ?i) (ELit ?c) =>
              let z0 := exW_assoc bs i in tacZ (z0 + c)%Z ltac:(exact (ex_ptr_val z0 c))
          | EExt _ _ _ _ =>
              let o := eval vm_compute in (exW_small v) in
              lazymatch o with
              | Some ?i => let z0 := exW_assoc bs i in tacZ z0 ltac:(apply (exW_small_sound E v i z0); [vm_cast_no_check (eq_refl o) | reflexivity | lia])
              end
          | _ => fail 100 "exW_cell: value form not supported:" v
          end
      | _ => fail 100 "exW_cell: no value at" rb rk
      end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exW_cs_idx_complete : forall r : reg, callee_saved r -> In (ridx r) exW_cs_idx.
Proof.
  intros r H. unfold callee_saved in H. unfold ridx. cbn [exW_cs_idx In].
  destruct H as [->|[->|[->|[->|[->|H]]]]]; [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
    | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity |].
  do 5 right. assert (E : exists z : Z, bv_unsigned r = z /\ (18 <= z <= 27)%Z) by (eexists; split; [reflexivity | exact H]).
  destruct E as (z & -> & Hz).
  assert (C : (z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27)%Z) by lia.
  repeat (destruct C as [C|C]; [subst z; cbn; tauto|]). subst z; cbn; tauto.
Qed.
(* [comment removed for export] *)
Lemma exW_cs_of_sr : forall (E : env) (sr : list expr) (r0 Rc : bvmap 5 word) (al : list (nat * expr)), regs_ok E sr Rc ->
  (forall k : nat, (k < 32)%nat -> ev E k = getr r0 (Z_to_bv 5 (Z.of_nat k))) ->
  Forall (fun ke => edenot E (snd ke) = ev E (fst ke)) al ->
  forallb (fun k => expr_eqb (nth k sr (ELit 0)) (EVar k) || existsb (fun ke => Nat.eqb (fst ke) k && expr_eqb (snd ke) (nth k sr (ELit 0))) al) exW_cs_idx = true ->
  cs_kept r0 Rc.
Proof.
  intros E sr r0 Rc al HR HE HA HB r Hr. pose proof (exW_cs_idx_complete r Hr) as Hin. rewrite forallb_forall in HB. specialize (HB _ Hin).
  rewrite (HR r). unfold sr_get.
  assert (N0 : bv_eqb r 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. unfold callee_saved in Hr. intros X.
    destruct Hr as [->|[->|[->|[->|[->|H]]]]]; try discriminate X. change (bv_unsigned (0 : reg)) with 0%Z in X. lia. }
  rewrite N0.
  assert (EV : edenot E (nth (ridx r) sr (ELit 0)) = ev E (ridx r)).
  { apply orb_true_iff in HB as [HB|HB].
    - apply expr_eqb_eq in HB. rewrite HB. reflexivity.
    - apply existsb_exists in HB as ([k e] & Hin' & Hke). cbn [fst snd] in Hke. apply andb_true_iff in Hke as [K1 K2].
      apply Nat.eqb_eq in K1. apply expr_eqb_eq in K2. subst k. rewrite <- K2.
      exact (proj1 (Forall_forall _ _) HA _ Hin'). }
  rewrite EV, (HE (ridx r) (ridx_range r)). f_equal. apply ridx_roundtrip.
Qed.
(* [comment removed for export] *)
Ltac exW_entry_vars := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; do 32 (destruct k as [|k]; [reflexivity|]); exfalso; lia.

(* [comment removed for export] *)
Ltac exW_regfactW r0 HRc r name :=
  lazymatch type of HRc with
  | regs_ok ?E ?sr ?Rc =>
      let e := eval vm_compute in (sr_get sr r) in
      lazymatch e with
      | EVar ?i =>
          let rg := eval cbv beta iota delta [nth ex_regs_list] in (nth i ex_regs_list ex_r1) in
          assert (name : getr Rc r = getr r0 rg) by (exact (reg_val _ _ _ r HRc))
      | _ => fail 100 "exW_regfactW: register" r "does not hold an entry value:" e
      end
  end.

(* [comment removed for export] *)
Lemma exW_kept_out : forall E (M M' : word -> option byte) (rb : expr) (b rlo rhi lo hi : Z),
  (forall a : word, ~ (lo <= bv_unsigned a < hi)%Z -> M' a = M a) -> edenot E rb = Z_to_bv 64 b -> (0 <= b < 2 ^ 64)%Z ->
  (b + rhi <= lo \/ hi <= b + rlo)%Z -> ex_region_kept E M M' (rb, rlo, rhi).
Proof.
  intros E M M' rb b rlo rhi lo hi OUT He Rb D. cbn [ex_region_kept]. rewrite He, u_Z2bv by lia. intros x Hx. apply OUT. lia.
Qed.

(* [comment removed for export] *)
Lemma exW_win_only : forall E (m : word -> option byte) log (rb : expr) (s F : Z), log_flat E log ->
  ex_in_regions [(rb, (- F)%Z, 0%Z)] log = true -> edenot E rb = Z_to_bv 64 s -> (0 <= s < 2 ^ 64)%Z ->
  forall x : word, ~ (s - F <= bv_unsigned x < s)%Z -> mem_denot E m log x = m x.
Proof.
  intros E m log rb s F Hlf Hreg Hb Rs x Hx.
  destruct (omem_eq_dec (mem_denot E m log x) (m x)) as [EQ|NE]; [exact EQ|]. exfalso. apply Hx.
  pose proof (ex_changed1 E m log rb (- F) 0 s Hlf Hreg Hb Rs x NE). lia.
Qed.
