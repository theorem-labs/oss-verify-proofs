(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5Core L5CoreSpecs L5Hp L5DivSpecs L5DivXP.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5DIVEARLY.
Import L5CS. Import L5DS. Import L5DIVXP.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition EARLY : Z := 0x21e54.
Definition DT2 : Z := 0x222d0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_sregs R R' i : regs_preserved R R' -> In i cs_all -> getr R' (reg i) = getr R (reg i).
Proof.
  intros RP Hi. apply RP. unfold callee_saved_idx. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [cbn; tauto|]). destruct Hi.
Qed.
Lemma u64_at_agree1 M M' a v : (forall i, a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros HA Ha H8 Hu. eapply (L5C.u64_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact Hu. Qed.
Lemma u8_at_agree1 M M' a v : (forall i, a <= i < a + 1 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v.
Proof. intros HA Ha H1 Hu. eapply (L5C.u8_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact Hu. Qed.
Lemma defined_agree1 M M' a n : (forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.defined M a n -> L5.defined M' a n.
Proof. intros HA D i Hi. rewrite HA by lia. apply D. exact Hi. Qed.
Lemma big_at_agree1 M M' o b : (forall i, o <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  L5.big_at RSEGS M o b -> L5.big_at RSEGS M' o b.
Proof. intros HA Ho H32 OB. eapply (L5C.big_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact OB. Qed.
Lemma limbs_at_agree1 M M' q ws : (forall i, q <= i < q + 8 * Z.of_nat (length ws) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 -> L5.limbs_at RSEGS M q ws -> L5.limbs_at RSEGS M' q ws.
Proof. intros HA Hq Hn HL. eapply (L5C.limbs_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact HL. Qed.
Lemma model_ok_but_vm m m' : model_ok m -> model_but_vm m m' -> model_ok m'.
Proof.
  intros (A & B & C) H. split. rewrite (L5C.halted_but_vm _ _ H). exact A. split. rewrite (L5C.lazy_but_vm _ _ H). exact B.
  rewrite (L5C.materialized_but_vm _ _ H). exact C.
Qed.
Lemma mod16_mod8 q : q mod 16 = 0 -> q mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod q 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (q / 16)) with ((2 * (q / 16)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma mem_eq (M M' : word -> option byte) : (forall a, M' a = M a) -> M' = M.
Proof. intros H. apply functional_extensionality. exact H. Qed.
Lemma div_saves_kept M M' sp R : (forall i, sp - 104 <= i < sp -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= sp - 104 -> sp <= 2 ^ 64 ->
  div_saves M sp R -> div_saves M' sp R.
Proof.
  intros HA Hlo Hhi (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13). unfold div_saves.
  repeat split; (eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]).
Qed.
Lemma outside1 lo n a : ~ (lo <= a < lo + n) -> L5.outside [(lo, n)] a.
Proof. intros H rg [<-|[]]. unfold L5.in_rng. cbn. exact H. Qed.
Lemma outside2 lo n lo' n' a : ~ (lo <= a < lo + n) -> ~ (lo' <= a < lo' + n') -> L5.outside [(lo, n); (lo', n')] a.
Proof. intros H H' rg [<-|[<-|[]]]; unfold L5.in_rng; cbn; assumption. Qed.
Lemma outside3 lo n lo' n' lo'' n'' a : ~ (lo <= a < lo + n) -> ~ (lo' <= a < lo' + n') -> ~ (lo'' <= a < lo'' + n'') -> L5.outside [(lo, n); (lo', n'); (lo'', n'')] a.
Proof. intros H H' H'' rg [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn; assumption. Qed.
(* [comment removed for export] *)
Lemma obj_limbs_agree1 M M' b ws :
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> forall i, q <= i < q + 8 * Z.of_nat (length ws) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> 0 <= q /\ q + 8 * Z.of_nat (length ws) <= 2 ^ 64) ->
  L5C.obj_limbs RSEGS M b ws -> L5C.obj_limbs RSEGS M' b ws.
Proof.
  intros HA HB (Ln & F & S). split. exact Ln. split. exact F. destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E. exact S.
  destruct (HB cap q eq_refl) as [H1 H2]. eapply limbs_at_agree1. apply (HA cap q eq_refl). exact H1. exact H2. exact S.
Qed.

Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
(* [comment removed for export] *)
Local Ltac kreg K i H := etransitivity; [exact (K i ltac:(inl)) | exact H].
Local Ltac uSCR := unfold DIV_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac prune_mod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; prune_mod; lia.
Local Ltac fsclia := prune_impl; prune_disj; prune_mod; uSCR; lia.
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].

Lemma DIV_SCR_val : DIV_SCR = 8848. Proof. reflexivity. Qed.
Lemma ASSIGN_SCR_val : ASSIGN_SCR = 8480. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition VdE (sp X Q f38 qneg sgn f69 : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 33%nat => X | 35%nat => Q | 38%nat => f38 | 61%nat => qneg | 62%nat => sgn | 69%nat => f69
  | _ => 0
  end.

(* [comment removed for export] *)
Definition early_fb (fbx fbn : Z) (n : nat) (sgn : Z) : Z := Z.lor (Z.land (assign_fb fbx fbn n false) 253) sgn.

(* [comment removed for export] *)
Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis ASSIGN : assign_spec L HI.

Lemma IMG : hl_img_hi L = 0x91000. Proof. apply (ly_img_hi L LY). Qed.
Lemma IMGLO : hl_img_lo L = 0x10000. Proof. apply (ly_img_lo L LY). Qed.
Lemma ERRNOV : hl_errno L = 0x70394. Proof. apply (ly_errno L LY). Qed.
Lemma LBdef LBx crx M VM : hi_heap HI LBx crx M VM -> forall A n, In (A, n) LBx ->
  L5.defined M A n /\ (4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A)) /\ A + n <= (hl_sptop L - 8388608) /\ 0 < n.
Proof. intros HH A n Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) (A, n) Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Dd & _). cbn in *. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma kept_above M M' LBx spd scr W a :
  L5C.hpres L LBx spd scr W M M' -> hl_sptop L - 2 ^ 23 + scr <= spd -> 0 <= scr -> 0x7fff80000000 <= hl_sptop L ->
  spd <= a < 2 ^ 64 -> L5.outside W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros HP H1 H2 H3 Ha OW. pose proof ERRNOV as EV.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply L5C.kept_stack; try assumption. rewrite EV. clear; lia.
Qed.
Lemma kept_inblock M M' LBx crx VM spd scr W A n a :
  hi_heap HI LBx crx M VM -> L5C.hpres L LBx spd scr W M M' -> In (A, n) LBx -> A <= a < A + n -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  L5.outside W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros HH HP Hin Ha SPT OW. pose proof (LBdef _ _ _ _ HH A n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
  pose proof ERRNOV as EV.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia.
  rewrite EV. clear - Aimg Ha. lia. exact OW.
Qed.
Lemma cdef_above M M' LBx spd scr W A n :
  L5C.hpres L LBx spd scr W M M' -> hl_sptop L - 2 ^ 23 + scr <= spd -> 0 <= scr -> 0x7fff80000000 <= hl_sptop L ->
  spd <= A -> A + n <= 2 ^ 64 -> L5.defined M A n -> L5.defined M' A n.
Proof.
  intros HP H1 H2 H3 HA HAn D i Hi. pose proof ERRNOV as EV.
  apply (L5C.hpres_cdef _ _ _ _ _ _ _ (A + i) HP). clear - H1 H2 H3 HA HAn Hi; lia. { right. left. unfold hl_ceil. clear - H1 H2 H3 HA HAn Hi. lia. }
  { unfold in_errno. rewrite EV. clear - H1 H2 H3 HA HAn Hi. lia. }
  apply D. exact Hi.
Qed.
Lemma cdef_below M M' LBx spd scr W A n :
  L5C.hpres L LBx spd scr W M M' -> hl_sptop L - 2 ^ 23 <= A -> A + n <= spd - scr -> 0 <= scr -> 0x7fff80000000 <= hl_sptop L -> spd <= 2 ^ 47 ->
  L5.defined M A n -> L5.defined M' A n.
Proof.
  intros HP H1 H2 H3 H4 H5 D i Hi. pose proof ERRNOV as EV.
  apply (L5C.hpres_cdef _ _ _ _ _ _ _ (A + i) HP). clear - H1 H2 H3 H4 H5 Hi; lia. { right. left. unfold hl_ceil. clear - H1 H2 H3 H4 H5 Hi. lia. }
  { unfold in_errno. rewrite EV. clear - H1 H2 H3 H4 H5 Hi. lia. }
  apply D. exact Hi.
Qed.
(* [comment removed for export] *)
Lemma hi_heap_stackwrite LBx crx M M' VM lo hi :
  hi_heap HI LBx crx M VM -> (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < hi) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  hl_sptop L - 2 ^ 23 <= lo -> hi <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L -> mem_grows M M' -> hi_heap HI LBx crx M' VM.
Proof.
  intros HH FR Hlo Hhi SPT MG. pose proof IMG as IMG'.
  eapply (L5C.hi_heap_client L SCFG HI LBx crx M M'). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG'; clear; lia. exact SPT.
  intros a Ha. destruct (Z_lt_le_dec a lo) as [Y|Y]. left; apply FR; [exact Ha | clear - Y; lia].
  destruct (Z_lt_le_dec a hi) as [U|U]. right; left; unfold hl_ceil; clear - Y U Hlo Hhi; lia. left; apply FR; [exact Ha | clear - U; lia]. exact MG.
Qed.

(* [comment removed for export] *)
Lemma early_path (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LBc : list (Z * Z)) (crc : credit)
      (sp X Q qneg sgn : Z) (bx bn : L5.bigobj) (wn : list Z) (Rs : bvmap 5 word) :
  (* [comment removed for export] *)
  getr R (reg 2) = Z_to_bv 64 (sp - 304) -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 qneg -> 0 <= qneg <= 1 -> getr R (reg 9) = Z_to_bv 64 Q ->
  getr R (reg 26) = Z_to_bv 64 sgn -> (sgn = 0 \/ sgn = 2) -> getr R (reg 27) = Z_to_bv 64 X ->
  (* [comment removed for export] *)
  hi_heap HI LBc crc M (m_vmmaps model) -> model_ok model -> K [] -> L5C.stk (hl_sptop L) M sp DIV_SCR ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M X bx -> Z.of_nat (L5.bo_len bx) <= 2 ^ 23 -> X mod 8 = 0 -> sp <= X -> X + 32 <= hl_sptop L -> L5.defined M X 32 ->
  (forall cap q, L5.bo_st bx = L5.BDyn cap q -> In (q, 8 * cap) LBc) ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M (sp - 168) bn -> L5C.obj_limbs RSEGS M bn wn -> L5.bo_len bn = L5.bo_len bx ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) LBc) ->
  (forall c q c' q', L5.bo_st bx = L5.BDyn c q -> L5.bo_st bn = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (* [comment removed for export] *)
  zero_obj M Q -> Q mod 8 = 0 -> sp <= Q -> Q + 32 <= hl_sptop L -> L5.defined M Q 32 -> (X + 32 <= Q \/ Q + 32 <= X) ->
  div_saves M sp Rs ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (q0 q1 : Z) (stx : L5.bstore),
      getr R' (reg 2) = Z_to_bv 64 (sp - 304) -> getr R' (reg 3) = Z_to_bv 64 GP -> getr R' (reg 4) = Z_to_bv 64 TP ->
      (forall i, In i [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg i) = getr R (reg i)) ->
      L5.big_at RSEGS M' Q (L5.BO (2 * qneg) 0 (L5.BInl q0 q1)) ->
      L5.big_at RSEGS M' X (L5.BO (early_fb (L5.bo_fb bx) (L5.bo_fb bn) (L5.bo_len bx) sgn) (L5.bo_len bx) stx) ->
      L5C.obj_limbs RSEGS M' (L5.BO (early_fb (L5.bo_fb bx) (L5.bo_fb bn) (L5.bo_len bx) sgn) (L5.bo_len bx) stx) wn ->
      match L5.bo_st bx, stx with
      | L5.BDyn c q, L5.BDyn c' q' => c' = c /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end ->
      L5.defined M' X 32 -> L5.defined M' Q 32 ->
      div_saves M' sp Rs -> (forall a, sp - 168 <= a < sp -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      L5C.hpres L LBc sp DIV_SCR [(X, 32); (L5.bo_data X bx, 8 * Z.of_nat (L5.bo_len bx)); (Q, 32)] M M' ->
      model_but_vm model model' -> hi_heap HI LBc crc M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (cfg R' DT2 M' model') K) ->
  srealizes RSEGS SCFG (cfg R EARLY M model) K.
Proof.
  intros H2 H3 H4 H8 Hq H9 H26 Hsg H27 HH MOK HK STK OBX LX23 AX8 SX HX DX BLX OBN OLN LEN BLN APB ZQ AQ8 SQ HQ DQ APQ DS KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & SCR0). rewrite DIV_SCR_val in SLO, SCR0.
  pose proof (proj1 MOK) as Mh. pose proof (proj1 (proj2 MOK)) as Ml.
  pose proof OBX as OB. unfold L5.big_at in OB. destruct OB as (Xf & Xfr & Xl & XST).
  pose proof OBN as ON. unfold L5.big_at in ON. destruct ON as (Nf & Nfr & Nl & NST).
  pose proof ZQ as OQ. unfold zero_obj, L5.big_at in OQ. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ. destruct OQ as (Qf & _ & Ql & _ & Q16 & Q24 & _).
  assert (WLN: length wn = L5.bo_len bx). { rewrite <- LEN. exact (proj1 OLN). }
  (* [comment removed for export] *)
  pose proof (dxe1_conc fx R M (VdE sp X Q 0 qneg sgn 0)) as P1. cbn [VdE] in P1.
  destruct (P1 ltac:(flia) ltac:(flia) H2 H9 ltac:(flia) A16
               ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0|flia|flia] | flia | flia]))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & A1 & A10 & A11 & C176 & C184 & C192 & C200)). clear P1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (hi_heap_stackwrite LBc crc M M1 _ (sp - 200) (sp - 200 + 32)). exact HH. exact FR1. flia. flia. flia. exact MG1. }
  (* [comment removed for export] *)
  eapply (ASSIGN fx1 R1 M1 model K LBc crc Q (sp - 200) (sp - 304) 0x21e70 (L5.BO 0 0 (L5.BInl 0 0)) (L5.BO 0 0 (L5.BInl 0 0)) [] HH1 MOK HK A10 A11).
  - cbn. clear; lia.
  - cbn. intros F; discriminate F.
  - cbn. intros F; exfalso; clear - F; lia.
  - exact A1.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { replace (sp - 304) with (sp + (-19) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. exact SPT. uSCR. eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. flia. flia.
  - eapply big_at_agree1. 4: exact ZQ. intros i Hi. apply FR1; flia. flia. flia.
  - exact AQ8. - flia. - exact HQ.
  - eapply L5.writable_grows. exact MG1. apply (L5C.writable_of_defined RSEGS). exact DQ. flia. flia.
  - cbn. intros cap q E. discriminate E.
  - unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact C200. split. clear; lia. split. exactA C192.
    split. reflexivity. split. exactA C184. split. exactA C176. clear; lia.
  - split. reflexivity. split. constructor. reflexivity.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - flia. - flia.
  - cbn. intros cap q E. discriminate E.
  - right. flia.
  - cbn. intros c q c' q' E. discriminate E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP2 & _ & GPOST). destruct g as [|A cap].
    2:{ exfalso. destruct GPOST as (_ & F & _). cbn in F. clear - F. lia. }
    destruct GPOST as (_ & -> & -> & (st1 & OQ2 & _ & SAME1) & HP2). cbn [L5.bo_fb L5.bo_st L5.bo_len L5.bo_data] in OQ2, SAME1, HP2.
    destruct st1 as [q0 q1|cq qq]. 2:{ contradiction. } clear SAME1.
    change (assign_fb 0 0 0 false) with 0 in OQ2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
    pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
    (* [comment removed for export] *)
    assert (KA2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha NQ. apply (kept_above M1 M2 LBc (sp - 304) ASSIGN_SCR _ a HP2). fsclia. uSCR; clear; lia. flia. exact Ha.
      apply outside2. exact NQ. clear; lia. }
    assert (KB2: forall A n a, In (A, n) LBc -> A <= a < A + n -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros A n a Hin Ha. pose proof (LBdef _ _ _ _ HH1 A n Hin) as (_ & _ & Ahi & _).
      apply (kept_inblock M1 M2 LBc crc _ (sp - 304) ASSIGN_SCR _ A n a HH1 HP2 Hin Ha SPT). apply outside2; flia. }
    assert (SCR2: L5.defined M2 (sp - 8848) 8848).
    { replace 8848 with (64 + (8480 + 304)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
      { eapply (cdef_below M1 M2 LBc (sp - 304) ASSIGN_SCR _ (sp - 8848) 64 HP2). flia. fsclia. uSCR; clear; lia. flia. flia.
        eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. flia. flia. }
      apply L5C.defined_app. 3: clear; lia.
      { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP2) as D. rewrite ASSIGN_SCR_val in D. exactA D. }
      eapply (cdef_above M1 M2 LBc (sp - 304) ASSIGN_SCR _ _ 304 HP2). fsclia. uSCR; clear; lia. flia. flia. flia.
      eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. flia. flia. }
    assert (DX2: L5.defined M2 X 32).
    { eapply (cdef_above M1 M2 LBc (sp - 304) ASSIGN_SCR _ X 32 HP2). fsclia. uSCR; clear; lia. flia. flia. flia. eapply L5.defined_grows. exact MG1. exact DX. }
    assert (DQ2: L5.defined M2 Q 32).
    { eapply (cdef_above M1 M2 LBc (sp - 304) ASSIGN_SCR _ Q 32 HP2). fsclia. uSCR; clear; lia. flia. flia. flia. eapply L5.defined_grows. exact MG1. exact DQ. }
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 (sp - 304)). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
    assert (E4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4. }
    assert (E8: getr R2 (reg 8) = Z_to_bv 64 qneg). { rewrite (preserved_sregs R1 R2 8 RP2) by inl. rewrite (K1 8%nat) by inl. exact H8. }
    assert (E9: getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
    assert (E27: getr R2 (reg 27) = Z_to_bv 64 X). { rewrite (preserved_sregs R1 R2 27 RP2) by inl. rewrite (K1 27%nat) by inl. exact H27. }
    pose proof OQ2 as (Qf2 & _ & Ql2 & _ & Q16' & Q24' & _).
    (* [comment removed for export] *)
    pose proof (dxe2_conc fx2 R2 M2 (VdE sp X Q 0 qneg sgn 0)) as P2. cbn [VdE] in P2.
    destruct (P2 ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(clear; lia) E2 E8 E9 E27 ltac:(flia) A16
                 ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR2|flia|flia] | flia | flia])
                 ltac:(eapply u8_at_agree1; [intros i Hi; apply KA2; flia | flia | flia | exact C200])
                 ltac:(flia) AQ8 ltac:(left; flia) Qf2 ltac:(clear; lia)
                 ltac:(apply (L5C.writable_of_defined RSEGS); [exact DQ2 | flia | flia]) Hq)
      as (fx3 & R3 & M3 & MG3 & _ & FR3 & (MS3 & K3 & B1 & B10 & B11 & CQ3)). clear P2.
    rewrite Z.land_0_l, Z.lor_0_l, Z.mod_small in CQ3 by (clear - Hq; lia).
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
    assert (HH3: hi_heap HI LBc crc M3 (m_vmmaps model2)).
    { eapply (hi_heap_stackwrite LBc crc M2 M3 _ Q (Q + 1)). exact HH2. intros i Hi Hn. apply FR3. exact Hi. clear - Hn; lia. flia. flia. flia. exact MG3. }
    (* [comment removed for export] *)
    assert (DRNG: forall a, sp - 304 <= a -> ~ (X <= a < X + 32) -> ~ (L5.bo_data X bx <= a < L5.bo_data X bx + 8 * Z.of_nat (L5.bo_len bx))).
    { intros a Ha NX. unfold L5.bo_data. destruct (L5.bo_st bx) as [v0 v1|c q]. { destruct XST as (_ & _ & _ & Hl & _). clear - NX Hl. lia. }
      pose proof (LBdef _ _ _ _ HH q (8 * c) (BLX c q eq_refl)) as (_ & _ & Ahi & _). destruct XST as (_ & _ & _ & Hl & _). clear - Ha Ahi Hl SLO. lia. }
    (* [comment removed for export] *)
    eapply (ASSIGN fx3 R3 M3 model2 K LBc crc X (sp - 168) (sp - 304) 0x21eb0 bx bn wn HH3 MOK2 HK B10 B11).
    + rewrite LEN. exact LX23.
    + rewrite LEN. unfold L5.bo_dyn, L5.bo_cap. destruct (L5.bo_st bx) as [v0 v1|c q].
      { destruct XST as (T & _). intros T'. rewrite T in T'. discriminate T'. } { destruct XST as (_ & _ & _ & Hl & _). intros _. exact Hl. }
    + rewrite LEN. unfold L5.bo_dyn. destruct (L5.bo_st bx) as [v0 v1|c q].
      { destruct XST as (_ & _ & _ & Hl & _). intros F. exfalso. clear - F Hl. lia. } { destruct XST as (T & _). intros _ T'. rewrite T in T'. discriminate T'. }
    + exact B1.
    + split. clear; lia. reflexivity.
    + kreg K3 2%nat E2.
    + kreg K3 4%nat E4.
    + split. { replace (sp - 304) with (sp + (-19) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
      split. fsclia. split. flia. split. exact SPT. uSCR. eapply L5.defined_grows. exact MG3. eapply L5.defined_sub. exact SCR2. flia. flia.
    + eapply big_at_agree1. 4: exact OBX. 2: flia. 2: flia. intros i Hi. rewrite FR3. rewrite KA2. apply FR1. flia. flia. flia. generalize APQ Hi; clear; lia. flia.
      generalize APQ Hi; clear; lia.
    + exact AX8. + flia. + exact HX.
    + apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG3. exact DX2. flia. flia.
    + exact BLX.
    + eapply big_at_agree1. 4: exact OBN. 2: flia. 2: flia. intros i Hi. rewrite FR3. rewrite KA2. apply FR1. flia. flia. flia. flia. flia. flia.
    + eapply obj_limbs_agree1. 3: exact OLN.
      * intros cap q E i Hi. rewrite WLN in Hi. unfold L5.big_at in OBN. rewrite E in NST. destruct NST as (_ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite LEN in Hlc.
        pose proof (LBdef _ _ _ _ HH q (8 * cap) (BLN cap q E)) as (_ & _ & Ahi & _).
        rewrite FR3. rewrite (KB2 q (8 * cap) i (BLN cap q E)). apply FR1. clear - Hi Qlo Qhi Hlc Hcap; lia. clear - Hi Hlc Ahi SLO; lia. clear - Hi Hlc; lia.
        clear - Hi Qlo Qhi Hlc Hcap; lia. clear - Hi Hlc Ahi SLO SQ; lia.
      * intros cap q E. rewrite WLN. rewrite E in NST. destruct NST as (_ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite LEN in Hlc. clear - Qlo Qhi Hlc Hcap. lia.
    + rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
    + flia. + flia.
    + exact BLN.
    + right. flia.
    + exact APB.
    + (* [comment removed for export] *)
      intros fx4 R4 M4 model4 g2 LB4 cr4 POST2 MBV4 HH4.
      destruct POST2 as (RP4 & _ & GP2). destruct g2 as [|A cap].
      2:{ exfalso. destruct GP2 as (Fd & F3 & _). rewrite LEN in F3. unfold L5.bo_dyn in Fd. destruct (L5.bo_st bx) as [v0 v1|c q].
        destruct XST as (_ & _ & _ & Hl & _). clear - F3 Hl. lia. destruct XST as (T & _). rewrite T in Fd. discriminate Fd. }
      destruct GP2 as (_ & -> & -> & (st2 & OX4 & OL4 & SAME2) & HP4). rewrite LEN in OX4, OL4, HP4. rewrite Z.max_id in HP4.
      set (f38 := assign_fb (L5.bo_fb bx) (L5.bo_fb bn) (L5.bo_len bx) false) in *.
      pose proof (model_ok_but_vm _ _ MOK2 MBV4) as MOK4. pose proof MOK4 as (Mh4 & Ml4 & _).
      pose proof OX4 as OX4'. unfold L5.big_at in OX4'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OX4'. destruct OX4' as (Xf4 & F38 & Xl4 & XST4).
      (* [comment removed for export] *)
      assert (KA4: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha NX. apply (kept_above M3 M4 LBc (sp - 304) ASSIGN_SCR _ a HP4). fsclia. uSCR; clear; lia. flia. exact Ha.
        apply outside2. exact NX. apply DRNG. clear - Ha; lia. exact NX. }
      assert (KB4: forall A n a, In (A, n) LBc -> A <= a < A + n -> ~ (L5.bo_data X bx <= a < L5.bo_data X bx + 8 * Z.of_nat (L5.bo_len bx)) ->
                   M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros A n a Hin Ha ND. pose proof (LBdef _ _ _ _ HH3 A n Hin) as (_ & _ & Ahi & _).
        apply (kept_inblock M3 M4 LBc crc _ (sp - 304) ASSIGN_SCR _ A n a HH3 HP4 Hin Ha SPT). apply outside2. flia. exact ND. }
      assert (DX4: L5.defined M4 X 32).
      { eapply (cdef_above M3 M4 LBc (sp - 304) ASSIGN_SCR _ X 32 HP4). fsclia. uSCR; clear; lia. flia. flia. flia. eapply L5.defined_grows. exact MG3. exact DX2. }
      assert (DQ4: L5.defined M4 Q 32).
      { eapply (cdef_above M3 M4 LBc (sp - 304) ASSIGN_SCR _ Q 32 HP4). fsclia. uSCR; clear; lia. flia. flia. flia. eapply L5.defined_grows. exact MG3. exact DQ2. }
      assert (F2: getr R4 (reg 2) = Z_to_bv 64 (sp - 304)). { rewrite (preserved_sregs R3 R4 2 RP4) by inl. rewrite (K3 2%nat) by inl. exact E2. }
      assert (F26: getr R4 (reg 26) = Z_to_bv 64 sgn).
      { rewrite (preserved_sregs R3 R4 26 RP4) by inl. rewrite (K3 26%nat) by inl. rewrite (preserved_sregs R1 R2 26 RP2) by inl. rewrite (K1 26%nat) by inl. exact H26. }
      assert (F27: getr R4 (reg 27) = Z_to_bv 64 X). { rewrite (preserved_sregs R3 R4 27 RP4) by inl. rewrite (K3 27%nat) by inl. exact E27. }
      (* [comment removed for export] *)
      pose proof (dxe3_conc fx4 R4 M4 (VdE sp X Q f38 qneg sgn 0)) as P3. cbn [VdE] in P3.
      destruct (P3 ltac:(flia) ltac:(flia) ltac:(clear - F38; lia) ltac:(clear - Hsg; lia) F2 F26 F27 ltac:(flia) A16 ltac:(flia) AX8 ltac:(left; flia) Xf4
                   ltac:(clear - F38; lia) ltac:(apply (L5C.writable_of_defined RSEGS); [exact DX4 | flia | flia]) ltac:(clear - Hsg; lia))
        as (fx5 & R5 & M5 & MG5 & _ & FR5 & (MS5 & K5 & _ & CX5)). clear P3.
      eapply (L5.cps_of_msteps RSEGS). exact Mh4. exact Ml4. exact MS5.
      (* [comment removed for export] *)
      assert (KEEP: forall a, sp - 168 <= a < sp -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. rewrite FR5. rewrite KA4. rewrite FR3. rewrite KA2. apply FR1. flia. flia. flia. flia. flia. flia. flia. flia. flia. flia. }
      (* [comment removed for export] *)
      assert (CEIL: hl_ceil L <= sp - DIV_SCR). { unfold hl_ceil. rewrite DIV_SCR_val. clear - SLO. lia. }
      assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L).
      { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
      assert (NSCR: forall W a, L5C.kept L LBc sp DIV_SCR W a -> ~ (sp - DIV_SCR <= a < sp)).
      { intros W a KA. eapply L5HP.kept_not_in_scratch. exact KA. exact LBceil. exact CEIL. unfold hl_ceil. rewrite IMG'. clear - SPT; lia. }
      set (W := [(X, 32); (L5.bo_data X bx, 8 * Z.of_nat (L5.bo_len bx)); (Q, 32)]).
      assert (HPA: L5C.hpres L LBc sp DIV_SCR W M M1).
      { eapply (L5HP.hpres_piece L LBc sp DIV_SCR W M M1 (fun a => sp - 200 <= a < sp - 200 + 32)). exact FR1.
        intros a KA C. apply (NSCR W a KA). rewrite DIV_SCR_val. clear - C; lia. rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0. exact MG1. }
      assert (HPB: L5C.hpres L LBc sp DIV_SCR W M M2).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M1 M2 (sp - 304) ASSIGN_SCR). exact HPA. exact HP2.
        - intros a KA. eapply L5HP.kept_mono. exact KA. intros b Hb; exact Hb. fsclia. flia.
          intros OW. apply outside2. apply (L5HP.outside_in _ _ Q 32 OW). subst W; cbn. right; right; left; reflexivity. clear; lia.
        - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      assert (HPC: L5C.hpres L LBc sp DIV_SCR W M M3).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M2 M3 sp DIV_SCR W). exact HPB.
        - eapply (L5HP.hpres_piece L LBc sp DIV_SCR W M2 M3 (fun a => Q <= a < Q + 1)). { intros a Ha Hn. apply FR3. exact Ha. clear - Hn; lia. }
          intros a KA C. apply (L5HP.outside_in _ _ Q 32 (L5HP.kept_outside_W _ _ _ _ _ _ KA)). subst W; cbn. right; right; left; reflexivity. clear - C; lia.
          rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG3. exact SCR2. exact MG3.
        - intros a KA; exact KA. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      assert (HPD: L5C.hpres L LBc sp DIV_SCR W M M4).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M3 M4 (sp - 304) ASSIGN_SCR). exact HPC. exact HP4.
        - intros a KA. eapply L5HP.kept_mono. exact KA. intros b Hb; exact Hb. fsclia. flia.
          intros OW. apply outside2. apply (L5HP.outside_in _ _ X 32 OW). subst W; cbn. left; reflexivity.
          apply (L5HP.outside_in _ _ _ _ OW). subst W; cbn. right; left; reflexivity.
        - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HPD) as SCR4.
      assert (HPE: L5C.hpres L LBc sp DIV_SCR W M M5).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M4 M5 sp DIV_SCR W). exact HPD.
        - eapply (L5HP.hpres_piece L LBc sp DIV_SCR W M4 M5 (fun a => X <= a < X + 1)). { intros a Ha Hn. apply FR5. exact Ha. clear - Hn; lia. }
          intros a KA C. apply (L5HP.outside_in _ _ X 32 (L5HP.kept_outside_W _ _ _ _ _ _ KA)). subst W; cbn. left; reflexivity. clear - C; lia.
          eapply L5.defined_grows. exact MG5. exact SCR4. exact MG5.
        - intros a KA; exact KA. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      (* [comment removed for export] *)
      apply (KONT fx5 R5 M5 model4 q0 q1 st2).
      * rewrite (K5 2%nat) by inl. exact F2.
      * rewrite (K5 3%nat) by inl. rewrite (preserved_sregs R3 R4 3 RP4) by inl. rewrite (K3 3%nat) by inl.
        rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3.
      * rewrite (K5 4%nat) by inl. rewrite (preserved_sregs R3 R4 4 RP4) by inl. rewrite (K3 4%nat) by inl. exact E4.
      * intros i Hi. cbn in Hi.
        repeat (destruct Hi as [<-|Hi];
          [ rewrite K5 by inl; rewrite (preserved_sregs R3 R4 _ RP4) by inl; rewrite K3 by inl; rewrite (preserved_sregs R1 R2 _ RP2) by inl;
            rewrite K1 by inl; reflexivity |]). destruct Hi.
      * (* [comment removed for export] *)
        unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
        assert (KQ: forall a, Q + 1 <= a < Q + 32 -> M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
        { intros a Ha. rewrite FR5. rewrite KA4. apply FR3. flia. flia. flia. generalize APQ Ha; clear; lia. flia. generalize APQ Ha; clear; lia. }
        split. { eapply u8_at_agree1. 4: exact CQ3. intros i Hi. rewrite FR5. apply KA4. flia. generalize APQ Hi; clear; lia. flia. generalize APQ Hi; clear; lia. flia. flia. }
        split. clear - Hq; lia. split. { eapply u64_at_agree1. 4: exact Ql2. intros i Hi; apply KQ; flia. flia. flia. }
        split. apply Z.testbit_even_0.
        split. { eapply u64_at_agree1. 4: exact Q16'. intros i Hi; apply KQ; flia. flia. flia. }
        split. { eapply u64_at_agree1. 4: exact Q24'. intros i Hi; apply KQ; flia. flia. flia. }
        destruct (proj2 (proj2 (proj2 OQ2))) as (_ & _ & _ & _ & R0' & R1'). split. clear; lia. split. exact R0'. exact R1'.
      * (* [comment removed for export] *)
        assert (SB0: Z.testbit sgn 0 = false). { destruct Hsg as [-> | ->]; reflexivity. }
        assert (EFB: Z.lor (Z.land f38 253) sgn = early_fb (L5.bo_fb bx) (L5.bo_fb bn) (L5.bo_len bx) sgn) by reflexivity.
        rewrite EFB in CX5.
        assert (KX: forall a, X + 1 <= a < X + 32 -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)). { intros a Ha. apply FR5. flia. clear - Ha; lia. }
        unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact CX5.
        split. { rewrite <- EFB. apply lor_byte. apply land_byte. clear - F38; lia. clear; lia. clear - Hsg; lia. }
        split. { eapply u64_at_agree1. 4: exact Xl4. intros i Hi; apply KX; flia. flia. flia. }
        destruct st2 as [u0 u1|c' q'].
        -- destruct XST4 as (T0 & U16 & U24 & REST). split. { rewrite <- EFB, Z.lor_spec, Z.land_spec, T0, SB0. reflexivity. }
           split. { eapply u64_at_agree1. 4: exact U16. intros i Hi; apply KX; flia. flia. flia. }
           split. { eapply u64_at_agree1. 4: exact U24. intros i Hi; apply KX; flia. flia. flia. } exact REST.
        -- destruct XST4 as (T0 & U16 & U24 & REST). split. { rewrite <- EFB, Z.lor_spec, Z.land_spec, T0. reflexivity. }
           split. { eapply u64_at_agree1. 4: exact U16. intros i Hi; apply KX; flia. flia. flia. }
           split. { eapply u64_at_agree1. 4: exact U24. intros i Hi; apply KX; flia. flia. flia. } exact REST.
      * (* [comment removed for export] *)
        eapply obj_limbs_agree1. 3: exact OL4.
        -- cbn [L5.bo_st]. intros cap q E i Hi. subst st2. rewrite WLN in Hi.
           destruct (L5.bo_st bx) as [v0 v1|c q0'] eqn:EBX. contradiction. destruct SAME2 as [-> ->].
           pose proof (LBdef _ _ _ _ HH q0' (8 * c) (BLX c q0' eq_refl)) as (_ & _ & Ahi & _). destruct XST as (_ & _ & _ & Hlc & _ & _ & Qlo & Qhi & _).
           apply FR5. clear - Hi Hlc Qlo Qhi; lia. clear - Hi Hlc Ahi SLO SX; lia.
        -- cbn [L5.bo_st]. intros cap q E. subst st2. rewrite WLN. destruct XST4 as (_ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). clear - Hlc Hcap Qlo Qhi. lia.
      * exact SAME2.
      * eapply L5.defined_grows. exact MG5. exact DX4.
      * eapply L5.defined_grows. exact MG5. exact DQ4.
      * eapply div_saves_kept. 4: exact DS. intros i Hi. apply KEEP. flia. flia. flia.
      * exact KEEP.
      * exact HPE.
      * exact (L5C.model_but_vm_trans _ _ _ MBV2 MBV4).
      * eapply (hi_heap_stackwrite LBc crc M4 M5 _ X (X + 1)). exact HH4. intros i Hi Hn. apply FR5. exact Hi. clear - Hn; lia. flia. flia. flia. exact MG5.
Qed.

End WithHeap.
End SCFG_1.
End L5DIVEARLY.
