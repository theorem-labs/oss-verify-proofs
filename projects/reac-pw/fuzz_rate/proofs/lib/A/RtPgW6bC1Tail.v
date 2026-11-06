(* Modified by Theorem Labs, 2026-10: the shadow entry over e and the regions based at F follow
   proofs/reac-pw/fuzz_role/lib/A/RPgEntBKit.v at 1fdaf126acfb (eb_SH, eb_shok, eb_rE), and reading a
   stored value back out of a final region follows proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4 (tl_val_at), for
   reac-pw/fuzz_rate's image A: rate's pcs, registers and cells; e is two written regions (the header and the three
   bytes after the copied string). *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the tail of ent_build's
   case 1 (pod.h:215-217, 290-294) inside LLVMFuzzerTestOneInput, from __asan_memcpy's return 0x81a94 to the join J
   0x81e00. Proves no function (kind: segment lemma).
   THE CODE (s1 = R, s2 = SHADOW_OFF, s6 = the kind byte sign-extended, s7 = s8 = l, s9 = F + 0xf8 = e.body):
     0x81a94  a0 := s7 + 1; a1 := s9 + s7; sb zero,0(a1)          e.body[l] := NUL (no check)
              ld a2,0x138(s1) (= F + 0xf0); sw 8,0(a2); sw a0,4(a2)  e.type = POD_STRING, e.size = l + 1
     0x81ab0  bgez s6 -> 0x81ce0                                     kind < 128
     0x81ab4  ld s11,0xc0(s1); bltu 0x5d,s8 -> 0x81ce4 (never: l <= 18)
     0x81ac0  a0 := [R+0x108] + l + 1; its check (covered); ld s6,0xe8(s1); sb 'x',0(a0)
     0x81ae4  a0 := a1 + 2; its check (covered); s8 := s10; sb zero,0(a0); s9 := l + 3; sw s9,4([R+0x138])
              ld s9,0x100(s1); ld s7,0xb0(s1); j 0x81660
     0x81ce0  ld s11,0xc0(s1); ld s6,0xe8(s1); ld s9,0x100(s1); j 0x81658; ld s7,0xb0(s1); s8 := s10
     0x81660  ld s10,0x118(s1); j 0x81e00
   HOW. One run per length l (the five lengths of the vocab strings: 12, 13, 14, 15, 18) with s7 and s8 pinned to l
   and s9 to F + 0xf8 (the extra env slot 32 is F), split at `bgez s6` by srr_branch_tok. The cells [R+0xb0, R+0x140)
   are a read-only region based at s1 (slots 33 = pp, 34 = vb, 35 = the cursor); e's header [F+0xf0, F+0xf8) and the
   three bytes [F+0xf8+l, F+0xfb+l) (zero at entry) are written regions based at F, in the frame (3, pos). The
   shadow entry [F+0xf0, F+0x158) at F covers the two checked stores (e is in scope: its shadow bytes are 0). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW6aBase RtPgW6bBase RtPgW6bC1Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions and remainders in this file (RtPgSteps.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the entry state ======================================== *)
Definition C1T_M4001 : Z := 18446744073709535231.   (* -0x4001 mod 2^64 *)
Lemma c1t_m4001 : -0x4001 mod 2 ^ 64 = C1T_M4001.
Proof. reflexivity. Qed.
Definition c1t_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0xb0 0x140 0 0
  [YP09.mkChunk 0xb0 (CVal 8 (SOff 33 0x4000)); YP09.mkChunk 0xc0 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0xe8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x100 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x108 (CVal 8 (SOff 32 0xf8)); YP09.mkChunk 0x118 (CVal 8 (SLit C1T_M4001));
   YP09.mkChunk 0x138 (CVal 8 (SOff 32 0xf0))].
Definition c1t_rH : YP09.region := YP09.mkRegion (Some 32%nat) 0xf0 0xf8 0xf0 0xf8 [].
Definition c1t_rT (l : Z) : YP09.region := YP09.mkRegion (Some 32%nat) (0xf8 + l) (0xfb + l) (0xf8 + l) (0xfb + l)
  [YP09.mkChunk (0xf8 + l) (CVal 1 (SLit 0)); YP09.mkChunk (0xf9 + l) (CVal 1 (SLit 0));
   YP09.mkChunk (0xfa + l) (CVal 1 (SLit 0))].
Definition c1t_SH : list shent := [mkSHE 32 0xf0 0x158].
Definition c1t_ss0 (l : Z) : sstate := mkSS C1_RCPY sr_atoms [c1t_rR; c1t_rH; c1t_rT l] None
  (mkFacts [c1_fR; c1_shf; (32%nat, mkAF 4096 0x7fffff800000 5)] [] []).
Definition c1t_extra (F pp vb cur : Z) : list word := [w64 F; w64 pp; w64 vb; w64 cur].
Definition c1t_clob : list (bv 5) := [10; 11; 12; 13; 22; 23; 24; 25; 26; 27]%bv.

(* ======================================== helpers ======================================== *)
Lemma c1t_val1_zero : forall m a, mbyte rsegs m a = Some (Z_to_bv 8 0) -> val_mem rsegs m a 1 0.
Proof.
intros m a H q Hq. assert (q = 0%nat) by lia. subst q. rewrite Z.add_0_r, H. reflexivity.
Qed.
(* a literal chunk of a final region, at its absolute address *)
Lemma c1t_lit_at : forall {fx : YK11.FPState} E ss H ms i r n b off (w : N) v a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w (SLit v))) (YP09.r_chunks r) ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> a = b + off ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat w) v.
Proof.
intros fx E ss H ms i r n b off w v a HS Hi Hb Hn Hc Hv Hw ->.
pose proof (rts_region_nth E ss ms i r H HS Hi) as HR. destruct r as [rb rlo rhi rwlo rwhi rcs].
cbn [YP09.r_base YP09.r_chunks] in Hb, Hc. subst rb.
pose proof (rts_chunks E _ n b rcs rlo rhi rwlo rwhi HR Hn _ Hc) as Hck.
exact (val_of_chunk_ok rsegs E _ b off w (SLit v) v Hck ltac:(reflexivity) Hv Hw).
Qed.
(* the bytes outside a run's write windows are kept *)
Lemma c1t_frame_kept : forall E rs (H : word -> bool) m m' (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a r, In r rs -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HP a Ha Hn. apply (aview_eq_of rsegs). apply HF. rewrite unsigned_lit_small by exact Ha.
intros (r & Hin & Hr). exact (Hn (HP a r Hin Hr)).
Qed.
Ltac c1t_in := cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* the entry state, for any length l *)
Lemma c1t_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc (R F l vb pp cur : Z),
  getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 -> getr regs 18 = w64 SHADOW_OFF ->
  12 <= l <= 18 -> 0 <= vb < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 -> 0 <= cur < 2 ^ 64 ->
  4096 <= F -> F + 512 <= 0x7fffff800000 -> F + 512 <= R -> F mod 32 = 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vb ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (F + 0xf8) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (-0x4001 mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
  (forall a, F + 0xf0 <= a < F + 0x158 -> apresent (w_H W) memc a) ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0xf8 + l + i) = Some (Z_to_bv 8 0)) ->
  st_ok rsegs (Ereg regs (c1t_extra F pp vb cur)) (c1t_ss0 l)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 C1_RCPY) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F l vb pp cur H9 HR0 HR1 HR16 H18 Hl Hvb Hpp0 Hpp1 Hcur HF0 HF1 HFR HF32
  Vb0 Vc0 Ve8 V100 V108 V118 V138 Hpe Hz.
set (E := Ereg regs (c1t_extra F pp vb cur)).
assert (U9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 vb) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cur) by (subst E; exact (ew_Ereg_extra regs _ 3)).
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
  + unfold region_ok, c1t_rR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs _ _ R 0xb0 8 (SOff 33 0x4000) (pp + 0x4000));
        [apply DO; [exact E33 | lia | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vb0].
    * apply (chunk_ok_val rsegs _ _ R 0xc0 8 (SOff 33 0) pp);
        [apply rts_den_atom; [exact E33 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vc0].
    * apply (chunk_ok_val rsegs _ _ R 0xe8 8 (SOff 34 0) vb);
        [apply rts_den_atom; [exact E34 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Ve8].
    * apply (chunk_ok_val rsegs _ _ R 0x100 8 (SOff 35 0) cur);
        [apply rts_den_atom; [exact E35 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V100].
    * apply (chunk_ok_val rsegs _ _ R 0x108 8 (SOff 32 0xf8) (F + 0xf8));
        [apply DO; [exact E32 | lia | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V108].
    * apply (chunk_ok_val rsegs _ _ R 0x118 8 (SLit C1T_M4001) C1T_M4001);
        [reflexivity | change (8 * Z.of_N 8) with 64; unfold C1T_M4001; lia | cbn; lia | rewrite <- c1t_m4001; exact V118].
    * apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 32 0xf0) (F + 0xf0));
        [apply DO; [exact E32 | lia | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact V138].
  + unfold region_ok, c1t_rH.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpe. lia.
  + unfold region_ok, c1t_rT.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable rsegs); apply Hpe; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs _ _ F (0xf8 + l) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply c1t_val1_zero. replace (F + (0xf8 + l)) with (F + 0xf8 + l + 0) by lia. apply Hz. lia.
    * apply (chunk_ok_val rsegs _ _ F (0xf9 + l) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply c1t_val1_zero. replace (F + (0xf9 + l)) with (F + 0xf8 + l + 1) by lia. apply Hz. lia.
    * apply (chunk_ok_val rsegs _ _ F (0xfa + l) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply c1t_val1_zero. replace (F + (0xfa + l)) with (F + 0xf8 + l + 2) by lia. apply Hz. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1t_rR, c1t_rH, c1t_rT.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
  split; [split; [lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; [exact I | exact I]]].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1t_ss0 ss_facts c1_shf c1_fR].
  split; [|split; exact I]. split; [|split; [|split; [|exact I]]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 4) with 16. lia.
  + apply (c1_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. change (2 ^ 5) with 32. lia.
Qed.

(* the shadow entry over e *)
Lemma c1t_shok : forall (regs : bvmap 5 word) (H : word -> bool) mem F pp vb cur,
  getr regs 18 = w64 SHADOW_OFF -> 4096 <= F -> in_app F 512 ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0xf0) 104 ->
  sh_ok rsegs C1_Bx c1t_SH (Ereg regs (c1t_extra F pp vb cur)) (mrestrict H mem).
Proof.
intros regs H mem F pp vb cur H18 HF0 Happ Hra.
pose proof asan_consts as (Hceil & _).
set (E := Ereg regs (c1t_extra F pp vb cur)).
assert (U18 : U E (SOff 18 0) = SHADOW_OFF).
{ apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; reflexivity | unfold SHADOW_OFF; lia]. }
assert (U32 : U E (SOff 32 0) = F).
{ apply U_atom; [subst E; exact (ew_Ereg_extra regs _ 0) | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; lia]. }
apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
unfold C1_Bx. rewrite U18, U32. split.
- rewrite <- (aview_rd_of rsegs). replace (0x158 - 0xf0) with 104 by lia. exact Hra.
- unfold app_apart. cbn [she_m she_lo she_hi]. unfold C1_Bx. rewrite U18, U32. intros a Ha.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* ---- 0x81a94 .. J, for one length l ---- *)
Ltac c1t_run HS0 HJ Hown HF U32' HAE KF ps :=
  pose proof (st_ok_pin_lit rsegs _ _ _ (23%bv : bv 5) _ HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; eassumption)) as HS1;
  pose proof (st_ok_pin_lit rsegs _ _ _ (24%bv : bv 5) _ HS1 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; eassumption)) as HS2;
  pose proof (st_ok_pin_sv rsegs _ _ _ (25%bv : bv 5) (SOff 32 0xf8) HS2 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; eassumption)) as HS;
  clear HS0 HS1 HS2;
  unfold cfg_at; change (w64 C1_RCPY) with (Z_to_bv 64 C1_RCPY);
  aj_run_to_tok w6_tbl_ok HS HJ KF C1_span W6_J;
  [ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
    apply awr_ok_cons_ro; [cbn; lia|];
    eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat ps 0);
      [reflexivity | rewrite U32'; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia |];
    eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat ps 0);
      [reflexivity | rewrite U32'; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]
  | ].

Lemma c1_tail : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos l vb pp cur kd : Z) (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> F = frame_addr lyc 3 pos ->
  getr regs 9 = w64 R -> alloc_ceiling <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 22 = w64 (c1_s6 kd) -> 0 <= kd < 256 ->
  getr regs 23 = w64 l -> getr regs 24 = w64 l -> getr regs 25 = w64 (F + 0xf8) ->
  (l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 18) ->
  0 <= vb < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 -> 0 <= cur < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vb ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (F + 0xf8) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (-0x4001 mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0xf8 + l + i) = Some (Z_to_bv 8 0)) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 104 ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1t_clob -> getr regs1 rg = getr regs rg) ->
    getr regs1 22 = w64 vb -> getr regs1 23 = w64 (pp + 0x4000) -> getr regs1 26 = w64 (-0x4001) ->
    getr regs1 27 = w64 pp -> getr regs1 25 = w64 cur -> getr regs1 24 = getr regs 26 ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0xf0) 4 8 ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0xf4) 4 (if Z.testbit kd 7 then l + 3 else l + 1) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0xf8 + l) 1 0 ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0xf9 + l) 1 (if Z.testbit kd 7 then 120 else 0) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (F + 0xfa + l) 1 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0xf8) -> ~ (F + 0xf8 + l <= a < F + 0xfb + l) ->
      aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    SRr rsegs W (cfg_at rsegs W6_J regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs C1_RCPY regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos l vb pp cur kd Q HJ Hown HF
  H9 HR0 HR1 HR16 H18 H22 Hkd H23 H24 H25 Hl Hvb Hpp0 Hpp1 Hcur Vb0 Vc0 Ve8 V100 V108 V118 V138 Hz Hra K.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs. pose proof LAWS as HL.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (Hceil & _).
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF32 & HFapp & HFpres & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF4096 & HFceil & _).
rewrite <- HF in HF32, HFapp, HFpres, HF4096, HFceil.
change (fs_frame_bytes 3) with 512 in HFapp, HFpres, HFceil.
assert (Hpe : forall a, F + 0xf0 <= a < F + 0x158 -> apresent (w_H W) memc a) by (intros a Ha; apply (proj1 (HFpres a ltac:(lia)))).
assert (Hl' : 12 <= l <= 18) by lia.
pose proof (c1t_entry W regs memc R F l vb pp cur H9 ltac:(lia) HR1 HR16 H18 Hl' Hvb Hpp0 Hpp1 Hcur HF4096 ltac:(lia) ltac:(lia) HF32
  Vb0 Vc0 Ve8 V100 V108 V118 V138 Hpe Hz) as HS0.
pose proof (c1t_shok regs (w_H W) memc F pp vb cur H18 HF4096 HFapp Hra) as SHOK.
set (E := Ereg regs (c1t_extra F pp vb cur)) in HS0, SHOK.
assert (HAE : env_agree 32 (Ereg regs (c1t_extra F pp vb cur)) E) by (subst E; apply env_agree_refl).
assert (E22 : ew E 22 = Z_to_bv 64 (c1_s6 kd)) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = getr regs 26) by (subst E; apply (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 vb) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cur) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (D22 : sv_denot E (SOff 22 0) = Z_to_bv 64 (c1_s6 kd)) by (cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (D25 : sv_denot E (SOff 32 0xf8) = getr regs 25).
{ rewrite H25. apply bv_eq. rewrite denot_SOff, U32. unfold w64. rewrite !unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia. }
clearbody E.
(* the bytes a final state keeps, the windows being e's header and the three bytes *)
set (P := fun a => F + 0xf0 <= a < F + 0xf8 \/ F + 0xf8 + l <= a < F + 0xfb + l).
destruct Hl as [->|[->|[->|[->| ->]]]].
all: c1t_run HS0 HJ Hown HF U32 HAE SHOK pos.
all: lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m0) (mrestrict _ ?mm) |- _ =>
  let rs' := eval vm_compute in rs in change rs with rs' in HFr;
  pose proof (c1t_frame_kept _ _ _ _ _ P HFr) as KR1;
  clear HFr
end.
all: lazymatch type of KR1 with (?X -> _) =>
  assert (KX : X); [intros a rg Hin Hr; cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32 in Hr; subst P; cbv beta; lia |];
  specialize (KR1 KX); clear KX
end.
all: repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* bgez s6 at 0x81ab0 *)
all: srr_branch_tok w6_tbl_ok HS SHOK C1_span.
all: rewrite D22 in Hc; cbn [sv_denot] in Hc; rewrite (c1_bge_s6 kd Hkd) in Hc.
all: destruct (Z.testbit kd 7) eqn:Hb; cbn [negb] in Hc; try discriminate Hc; try rewrite Hb in K.
all: aj_run_to_tok w6_tbl_ok HS HJ SHOK C1_span W6_J.
all: try (lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0);
    [reflexivity | rewrite U32; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia |];
  eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0);
    [reflexivity | rewrite U32; rewrite HF; ring | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]).
all: lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?mm) |- _ =>
  let rs' := eval vm_compute in rs in change rs with rs' in HFr;
  pose proof (c1t_frame_kept _ _ _ _ _ P HFr) as KR2;
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
  replace (ss_pc ss) with W6_J by (vm_compute; reflexivity)
end.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 W6_J) mm (seg_rom rsegs)) md) with (cfg_at rsegs W6_J rg mm md) end.
all: apply K;
[ exact HJ
| c1_kio
| apply (regs_kept_of_st_ok rsegs _ _ _ regs (c1t_extra F pp vb cur) (w_H W) c1t_clob HS);
    [env_agree_chain HAE | vm_compute; reflexivity]
| c1_regv HS (22%bv : bv 5); rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1_regv HS (23%bv : bv 5); rewrite E33, unsigned_lit_small by lia; reflexivity
| c1_regv HS (26%bv : bv 5); unfold w64; rewrite <- (Z_to_bv_mod64 (-0x4001)); reflexivity
| c1_regv HS (27%bv : bv 5); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1_regv HS (25%bv : bv 5); rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1_regv HS (24%bv : bv 5); rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| eapply (c1t_lit_at _ _ _ _ 1%nat _ 32%nat F 0xf0 4 8);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1t_in | cbn; lia | cbn; lia | lia]
| eapply (c1t_lit_at _ _ _ _ 1%nat _ 32%nat F 0xf4 4);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1t_in | cbn; lia | cbn; lia | lia]
| lazymatch type of H23 with _ = w64 ?lv =>
  eapply (c1t_lit_at _ _ _ _ 2%nat _ 32%nat F (0xf8 + lv) 1 0);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1t_in | cbn; lia | cbn; lia | lia] end
| lazymatch type of H23 with _ = w64 ?lv =>
  eapply (c1t_lit_at _ _ _ _ 2%nat _ 32%nat F (0xf9 + lv) 1);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1t_in | cbn; lia | cbn; lia | lia] end
| lazymatch type of H23 with _ = w64 ?lv =>
  eapply (c1t_lit_at _ _ _ _ 2%nat _ 32%nat F (0xfa + lv) 1 0);
    [exact HS | vm_compute; reflexivity | reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | c1t_in | cbn; lia | cbn; lia | lia] end
| intros a Ha Hn1 Hn2; rewrite (KR2 a Ha ltac:(subst P; cbv beta; tauto)); exact (KR1 a Ha ltac:(subst P; cbv beta; tauto)) ].
Qed.
End d.
End b.

Print Assumptions c1_tail.
