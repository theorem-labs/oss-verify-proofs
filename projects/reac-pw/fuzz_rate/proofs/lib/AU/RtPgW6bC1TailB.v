(* Modified by Theorem Labs, 2026-10: the shadow entry over e and the regions based at F follow
   proofs/reac-pw/fuzz_role/lib/A/RPgEntBKit.v at 1fdaf126acfb (eb_SH, eb_shok, eb_rE), and reading a
   stored value back out of a final region follows proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4 (tl_val_at), for
   reac-pw/fuzz_rate's image A: rate's pcs, registers and cells; e is two written regions (the header and the three
   bytes after the copied string). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC1Tail.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the pcs, the registers and the real-frame cells are image B's; the pod object is e62
   (F + 0x210) in the class-4 frame (4, pos); the kind byte and what is left come from the spill cells [R+0x128] and
   [R+0x70]; the three UBSan tests against the cell [R+0x100] are decided by the engine from that cell's closed
   bounds; the prefix c1t_ becomes c1bt_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the tail of ent_build's
   case 1 (pod.h:215-217, 290-294) inside LLVMFuzzerTestOneInput, from __asan_memcpy's return 0x81bd4 to the join J
   0x820dc. Proves no function (kind: segment lemma).
   THE CODE (s1 = R, s4 = SHADOW_OFF, s2 = s6 = l, s8 = F + 0x218 = e62.body):
     0x81bd4  ld a0,0x100(s1) (= ~(F + 0x218)); 0x81bd8 bgeu a0,s2 (T3; else the `unimp`)
     0x81be0  a0 := s2 + 1; a1 := s8 + s2; sb zero,0(a1)            e62.body[l] := NUL (no check)
              ld a1,0x150(s1) (= F + 0x210); sw 8,0(a1); sw a0,4(a1) e62.type = POD_STRING, e62.size = l + 1
     0x81bfc  ld t1,0x70(s1) (what is left); ld a1,0x128(s1) (the kind byte, sign-extended)
     0x81c04  bgez a1 -> 0x81c78                                     kind < 128
     0x81c08  a1 := 93; bltu a1,s6 -> 0x81c78 (never: l <= 18)
     0x81c10  ld a1,0x100(s1); 0x81c14 bltu s2,a1 (T3); a0 := [R+0x130] + l + 1; its check (covered); sb 'x',0(a0)
     0x81c40  ld a0,0x100(s1); 0x81c44 bgeu a0,a1 (T3, a1 = l + 2); a0 := [R+0x130] + l + 2; its check (covered);
              sb zero,0(a0); s2 := l + 3; ld s6,0x150(s1); sw s2,4(s6); j 0x820d8
     0x820d8  ld s2,0x158(s1) (= pp + 0x4000) -> J 0x820dc
     0x81c78  ld s2,0x158(s1); ld s6,0x150(s1); j 0x820dc
   HOW. One run per length l (the five lengths of the vocab strings: 12, 13, 14, 15, 18) with s2 and s6 pinned to l
   and s8 to F + 0x218 (the extra env slot 32 is F), split at `bgez a1` by srr_branch_tok. The cells [R+0x70, R+0x160)
   are a read-only region based at s1 (slots 33 = pp + 0x4000, 34 = ~(F + 0x218) with its closed bounds, which decide
   the three T3 tests, 35 = what is left, 36 = the kind byte sign-extended); e62's header [F+0x210, F+0x218) and the
   three bytes [F+0x218+l, F+0x21b+l) (zero at entry) are written regions based at F, in the frame (4, pos). The
   shadow entry [F+0x210, F+0x278) at F covers the two checked stores (e62 is in scope: its shadow bytes are 0). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMemB RtPgStepsB RtPgW6bBaseB RtPgW6bC1KitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions and remainders in this file (RtPgStepsB.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the entry state ======================================== *)
Definition c1bt_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x70 0x160 0 0
  [YP09.mkChunk 0x70 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x100 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x128 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x218));
   YP09.mkChunk 0x150 (CVal 8 (SOff 32 0x210)); YP09.mkChunk 0x158 (CVal 8 (SOff 33 0))].
Definition c1bt_rH : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x218 0x210 0x218 [].
Definition c1bt_rT (l : Z) : YP09.region := YP09.mkRegion (Some 32%nat) (0x218 + l) (0x21b + l) (0x218 + l) (0x21b + l)
  [YP09.mkChunk (0x218 + l) (CVal 1 (SLit 0)); YP09.mkChunk (0x219 + l) (CVal 1 (SLit 0));
   YP09.mkChunk (0x21a + l) (CVal 1 (SLit 0))].
Definition c1bt_SH : list shent := [mkSHE 32 0x210 0x278].
Definition c1bt_ss0 (l : Z) : sstate := mkSS C1B_RCPY sr_atoms [c1bt_rR; c1bt_rH; c1bt_rT l] None
  (mkFacts [c1b_fR; c1b_shf; (32%nat, mkAF 4096 0x7fffff800000 5); (34%nat, mkAF C1B_NFLO C1B_NFHI 0)] [] []).
(* slots 32 .. 36: F, pp + 0x4000, ~(F + 0x218), what is left, the kind byte sign-extended (mod 2^64) *)
Definition c1bt_extra (F pp4 t s6v : Z) : list word :=
  [w64 F; w64 pp4; w64 (2 ^ 64 - 1 - (F + 0x218)); w64 t; w64 s6v].
(* s8 (24) is pinned to SOff 32 0x218 by the run, so it counts as changed *)
Definition c1bt_clob : list (bv 5) := [6; 10; 11; 12; 18; 22; 24]%bv.

(* ======================================== helpers ======================================== *)
Lemma c1bt_val1_zero : forall m a, mbyte rsegs m a = Some (Z_to_bv 8 0) -> val_mem rsegs m a 1 0.
Proof.
intros m a H q Hq. assert (q = 0%nat) by lia. subst q. rewrite Z.add_0_r, H. reflexivity.
Qed.
(* a literal chunk of a final region, at its absolute address *)
Lemma c1bt_lit_at : forall {fx : YK11.FPState} E ss H ms i r n b off (w : N) v a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w (SLit v))) (YP09.r_chunks r) ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> a = b + off ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat w) v.
Proof.
intros fx E ss H ms i r n b off w v a HS Hi Hb Hn Hc Hv Hw ->.
pose proof (rtsb_region_nth E ss ms i r H HS Hi) as HR. destruct r as [rb rlo rhi rwlo rwhi rcs].
cbn [YP09.r_base YP09.r_chunks] in Hb, Hc. subst rb.
pose proof (rtsb_chunks E _ n b rcs rlo rhi rwlo rwhi HR Hn _ Hc) as Hck.
exact (val_of_chunk_ok rsegs E _ b off w (SLit v) v Hck ltac:(reflexivity) Hv Hw).
Qed.
(* the bytes outside a run's write windows are kept *)
Lemma c1bt_frame_kept : forall E rs (H : word -> bool) m m' (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a r, In r rs -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HP a Ha Hn. apply (aview_eq_of rsegs). apply HF. rewrite unsigned_lit_small by exact Ha.
intros (r & Hin & Hr). exact (Hn (HP a r Hin Hr)).
Qed.
Ltac c1bt_in := cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* the entry state, for any length l *)
Lemma c1bt_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc (R F l pp4 t s6v : Z),
  getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 -> getr regs 20 = w64 SHADOW_OFF ->
  12 <= l <= 18 -> 0 <= pp4 < 2 ^ 64 -> 0 <= t < 2 ^ 64 -> 0 <= s6v < 2 ^ 64 ->
  4096 <= F -> F + 1024 <= 0x7fffff800000 -> F + 1024 <= R -> F mod 32 = 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 t ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 (2 ^ 64 - 1 - (F + 0x218)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x128) 8 s6v ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 pp4 ->
  (forall a, F + 0x210 <= a < F + 0x278 -> apresent (w_H W) memc a) ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x218 + l + i) = Some (Z_to_bv 8 0)) ->
  st_ok rsegs (Ereg regs (c1bt_extra F pp4 t s6v)) (c1bt_ss0 l)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 C1B_RCPY) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F l pp4 t s6v H9 HR0 HR1 HR16 H20 Hl Hpp Ht Hs6 HF0 HF1 HFR HF32
  V70 V100 V128 V130 V150 V158 Hpe Hz.
set (E := Ereg regs (c1bt_extra F pp4 t s6v)).
assert (U9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pp4) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - (F + 0x218))) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 t) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 s6v) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (DO : forall n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c)).
{ intros n v c Hn Hv Hvc. apply bv_eq. rewrite denot_SOff, Hn, !unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia. }
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
- apply regs_ok_Ereg.
- assert (Hc : l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 16 \/ l = 17 \/ l = 18) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok, c1bt_rR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs _ _ R 0x70 8 (SOff 35 0) t);
        [apply rtsb_den_atom; [exact E35 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V70].
    * apply (chunk_ok_val rsegs _ _ R 0x100 8 (SOff 34 0) (2 ^ 64 - 1 - (F + 0x218)));
        [apply rtsb_den_atom; [exact E34 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V100].
    * apply (chunk_ok_val rsegs _ _ R 0x128 8 (SOff 36 0) s6v);
        [apply rtsb_den_atom; [exact E36 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V128].
    * apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 32 0x218) (F + 0x218));
        [apply DO; [exact E32 | lia | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V130].
    * apply (chunk_ok_val rsegs _ _ R 0x150 8 (SOff 32 0x210) (F + 0x210));
        [apply DO; [exact E32 | lia | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V150].
    * apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 33 0) pp4);
        [apply rtsb_den_atom; [exact E33 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V158].
  + unfold region_ok, c1bt_rH.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpe. lia.
  + unfold region_ok, c1bt_rT.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable rsegs); apply Hpe; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs _ _ F (0x218 + l) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply c1bt_val1_zero. replace (F + (0x218 + l)) with (F + 0x218 + l + 0) by lia. apply Hz. lia.
    * apply (chunk_ok_val rsegs _ _ F (0x219 + l) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply c1bt_val1_zero. replace (F + (0x219 + l)) with (F + 0x218 + l + 1) by lia. apply Hz. lia.
    * apply (chunk_ok_val rsegs _ _ F (0x21a + l) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply c1bt_val1_zero. replace (F + (0x21a + l)) with (F + 0x218 + l + 2) by lia. apply Hz. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1bt_rR, c1bt_rH, c1bt_rT.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
  split; [split; [lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; [exact I | exact I]]].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bt_ss0 ss_facts c1b_shf c1b_fR].
  split; [|split; exact I]. split; [|split; [|split; [|split; [|exact I]]]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 4) with 16. lia.
  + apply (c1b_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. change (2 ^ 5) with 32. lia.
  + apply (c1b_af _ _ _ _ _ _ E34); [lia | unfold C1B_NFLO, C1B_NFHI; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
Qed.

(* the shadow entry over e62 *)
Lemma c1bt_shok : forall (regs : bvmap 5 word) (H : word -> bool) mem F pp4 t s6v,
  getr regs 20 = w64 SHADOW_OFF -> 4096 <= F -> in_app F 1024 ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0x210) 104 ->
  sh_ok rsegs C1B_Bx c1bt_SH (Ereg regs (c1bt_extra F pp4 t s6v)) (mrestrict H mem).
Proof.
intros regs H mem F pp4 t s6v H20 HF0 Happ Hra.
pose proof asan_consts as (Hceil & _).
set (E := Ereg regs (c1bt_extra F pp4 t s6v)).
assert (U20 : U E (SOff 20 0) = SHADOW_OFF).
{ apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; reflexivity | unfold SHADOW_OFF; lia]. }
assert (U32 : U E (SOff 32 0) = F).
{ apply U_atom; [subst E; exact (ew_Ereg_extra regs _ 0) | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; lia]. }
apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
unfold C1B_Bx. rewrite U20, U32. split.
- rewrite <- (aview_rd_of rsegs). replace (0x278 - 0x210) with 104 by lia. exact Hra.
- unfold app_apart. cbn [she_m she_lo she_hi]. unfold C1B_Bx. rewrite U20, U32. intros a Ha.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* ---- 0x81bd4 .. J, for one length l ---- *)
Ltac c1bt_run HS0 HJ Hown HF U32' HAE KF ps :=
  pose proof (st_ok_pin_lit rsegs _ _ _ (18%bv : bv 5) _ HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; eassumption)) as HS1;
  pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) _ HS1 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; eassumption)) as HS2;
  pose proof (st_ok_pin_sv rsegs _ _ _ (24%bv : bv 5) (SOff 32 0x218) HS2 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; eassumption)) as HS;
  clear HS0 HS1 HS2;
  unfold cfg_at; change (w64 C1B_RCPY) with (Z_to_bv 64 C1B_RCPY);
  aj_run_to_tok w6bb_tbl_ok HS HJ KF C1B_span W6BB_J;
  [ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
    apply awr_ok_cons_ro; [cbn; lia|];
    eapply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat ps 0);
      [reflexivity | rewrite U32'; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia |];
    eapply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat ps 0);
      [reflexivity | rewrite U32'; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]
  | ].

Lemma c1b_tail : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos l pp t kd : Z) (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (4, pos) own -> F = frame_addr lyc 4 pos ->
  getr regs 9 = w64 R -> alloc_ceiling <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 18 = w64 l -> getr regs 22 = w64 l -> getr regs 24 = w64 (F + 0x218) ->
  (l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 18) ->
  0 <= kd < 256 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 -> 0 <= t < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 t ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 (2 ^ 64 - 1 - (F + 0x218)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x128) 8 (c1b_s6 kd mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (pp + 0x4000) ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x218 + l + i) = Some (Z_to_bv 8 0)) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1bt_clob -> getr regs1 rg = getr regs rg) ->
    getr regs1 18 = w64 (pp + 0x4000) -> getr regs1 22 = w64 (F + 0x210) -> getr regs1 6 = w64 t ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0x210) 4 8 ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0x214) 4 (if Z.testbit kd 7 then l + 3 else l + 1) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0x218 + l) 1 0 ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0x219 + l) 1 (if Z.testbit kd 7 then 120 else 0) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0x21a + l) 1 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x210 <= a < F + 0x218) -> ~ (F + 0x218 + l <= a < F + 0x21b + l) ->
      aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    SRr rsegs W (cfg_at rsegs W6BB_J regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs C1B_RCPY regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos l pp t kd Q HJ Hown HF
  H9 HR0 HR1 HR16 H20 H18 H22 H24 Hl Hkd Hpp0 Hpp1 Ht V70 V100 V128 V130 V150 V158 Hz Hra K.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs. pose proof LAWS as HL.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (Hceil & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & HFapp & HFpres & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- HF in HF32, HFapp, HFpres, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in HFapp, HFpres, HFceil.
assert (Hpe : forall a, F + 0x210 <= a < F + 0x278 -> apresent (w_H W) memc a)
  by (intros a Ha; apply (proj1 (HFpres a ltac:(lia)))).
assert (Hl' : 12 <= l <= 18) by lia.
pose proof (c1b_s6_range kd Hkd) as Hs6r.
assert (Hs6m : 0 <= c1b_s6 kd mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
pose proof (c1bt_entry W regs memc R F l (pp + 0x4000) t (c1b_s6 kd mod 2 ^ 64) H9 ltac:(lia) HR1 HR16 H20 Hl'
  ltac:(lia) Ht Hs6m HF4096 ltac:(lia) ltac:(lia) HF32 V70 V100 V128 V130 V150 V158 Hpe Hz) as HS0.
pose proof (c1bt_shok regs (w_H W) memc F (pp + 0x4000) t (c1b_s6 kd mod 2 ^ 64) H20 HF4096 HFapp Hra) as SHOK.
set (E := Ereg regs (c1bt_extra F (pp + 0x4000) t (c1b_s6 kd mod 2 ^ 64))) in HS0, SHOK.
assert (HAE : env_agree 32 (Ereg regs (c1bt_extra F (pp + 0x4000) t (c1b_s6 kd mod 2 ^ 64))) E)
  by (subst E; apply env_agree_refl).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pp + 0x4000)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 t) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (c1b_s6 kd mod 2 ^ 64)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (D36 : sv_denot E (SOff 36 0) = Z_to_bv 64 (c1b_s6 kd)).
{ rewrite (rtsb_den_atom E 36 _ E36 Hs6m). apply Z_to_bv_mod64. }
assert (D24 : sv_denot E (SOff 32 0x218) = getr regs 24).
{ rewrite H24. apply bv_eq. rewrite denot_SOff, U32. unfold w64. rewrite !unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia. }
clearbody E.
(* the bytes a final state keeps, the windows being e62's header and the three bytes *)
set (P := fun a => F + 0x210 <= a < F + 0x218 \/ F + 0x218 + l <= a < F + 0x21b + l).
destruct Hl as [->|[->|[->|[->| ->]]]].
all: c1bt_run HS0 HJ Hown HF U32 HAE SHOK pos.
all: lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m0) (mrestrict _ ?mm) |- _ =>
  let rs' := eval vm_compute in rs in change rs with rs' in HFr;
  pose proof (c1bt_frame_kept _ _ _ _ _ P HFr) as KR1;
  clear HFr
end.
all: lazymatch type of KR1 with (?X -> _) =>
  assert (KX : X); [intros a rg Hin Hr; cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32 in Hr; subst P; cbv beta; lia |];
  specialize (KR1 KX); clear KX
end.
all: repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* bgez a1 at 0x81c04 *)
all: srr_branch_tok w6bb_tbl_ok HS SHOK C1B_span.
all: rewrite D36 in Hc; cbn [sv_denot] in Hc; rewrite (c1b_bge_s6 kd Hkd) in Hc.
all: destruct (Z.testbit kd 7) eqn:Hb; cbn [negb] in Hc; try discriminate Hc; try rewrite Hb in K.
all: aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C1B_span W6BB_J.
all: try (lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0);
    [reflexivity | rewrite U32; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia |];
  eapply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0);
    [reflexivity | rewrite U32; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]).
all: lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?mm) |- _ =>
  let rs' := eval vm_compute in rs in change rs with rs' in HFr;
  pose proof (c1bt_frame_kept _ _ _ _ _ P HFr) as KR2;
  clear HFr
end.
all: lazymatch type of KR2 with (?X -> _) =>
  assert (KX : X); [intros a rg Hin Hr; cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32 in Hr; subst P; cbv beta; lia |];
  specialize (KR2 KX); clear KX
end.
all: repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* at J *)
all: lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with W6BB_J by (vm_compute; reflexivity)
end.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 W6BB_J) mm (seg_rom rsegs)) md) with (cfg_at rsegs W6BB_J rg mm md) end.
all: apply K;
[ exact HJ
| c1b_kio
| apply (regs_kept_of_st_ok rsegs _ _ _ regs (c1bt_extra F (pp + 0x4000) t (c1b_s6 kd mod 2 ^ 64)) (w_H W) c1bt_clob HS);
    [env_agree_chain HAE | vm_compute; reflexivity]
| c1b_regv HS (18%bv : bv 5); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1b_regv HS (22%bv : bv 5); rewrite E32, unsigned_lit_small by lia; reflexivity
| c1b_regv HS (6%bv : bv 5); rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| eapply (c1bt_lit_at _ _ _ _ 1%nat _ 32%nat F 0x210 4 8);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1bt_in | cbn; lia | cbn; lia | lia]
| eapply (c1bt_lit_at _ _ _ _ 1%nat _ 32%nat F 0x214 4);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1bt_in | cbn; lia | cbn; lia | lia]
| lazymatch type of H18 with _ = w64 ?lv =>
  eapply (c1bt_lit_at _ _ _ _ 2%nat _ 32%nat F (0x218 + lv) 1 0);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1bt_in | cbn; lia | cbn; lia | lia] end
| lazymatch type of H18 with _ = w64 ?lv =>
  eapply (c1bt_lit_at _ _ _ _ 2%nat _ 32%nat F (0x219 + lv) 1);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1bt_in | cbn; lia | cbn; lia | lia] end
| lazymatch type of H18 with _ = w64 ?lv =>
  eapply (c1bt_lit_at _ _ _ _ 2%nat _ 32%nat F (0x21a + lv) 1 0);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1bt_in | cbn; lia | cbn; lia | lia] end
| intros a Ha Hn1 Hn2; rewrite (KR2 a Ha ltac:(subst P; cbv beta; tauto)); exact (KR1 a Ha ltac:(subst P; cbv beta; tauto)) ].
Qed.
End d.
End b.

Print Assumptions c1b_tail.
