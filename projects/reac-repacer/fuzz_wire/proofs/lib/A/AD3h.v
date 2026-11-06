(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane (S8) for another Theorem Labs lane's knock StackDepot chain. *)
(*
   StackDepot map-on-first-use chain: the contract of __sanitizer::MmapOrDie(unsigned long, char const*, bool)
   (0x65200-0x6530c in fuzz_wire.asan; the donor fuzz_knock.asan's 0x64278-0x64384, 67 insns, unstripped twin sha256 fff563b3...; AB1w.v tfib_A_MmapOrDie) and its proof.
   rule 24: proves function MmapOrDie (kind: runtime callee contract + its walk). Released-proof lookup
   and a second check found no released, delivered or
   in-flight proof of MmapOrDie for knock; msgpack-c lib/W2/F_mmapordie.v (another framework) was read as the template.
   The consumer, S7 (lib/A/AD3g.v, TwoLevelMap::Create), binds mod_contract by name.

   THE CODE (addresses of the donor fuzz_knock ASan image (pin sha256 61768cf4739b), not fuzz_wire.asan's; a0 = size, a1 = name, a2 = raw_report; flags MAP_PRIVATE|MAP_ANONYMOUS = 0x22, prot 3)
     0x64278 frame 48: sd ra/s0/s1/s2/s3 at sp+40..sp+8 (sp - 48 .. sp - 8 below the entry sp)
     0x64298 s3 := GOT 0x965b0 -> 0x12dfe0 (PageSizeCached); a1 := 4096 (nonzero: GetPageSize 0x642ac skipped)
     0x642b8 IsPowerOfTwo(4096) (the RawWrite + Die arm 0x64358 is not taken)
     0x642c4 s2 := (size + 4095) & -4096 = size (size page aligned)
     0x642d4 sw 0x22, 4(sp); jal GetNamedMappingFd 0x64f54 (name, s2, sp + 4): frame 272, 7 saves at its
             sp + 0xd8 .. sp + 0x110 (entry sp - 104 .. entry sp - 48); name <> 0, then common_flags GOT 0x965c0 ->
             0x130068 and decorate_proc_maps (byte 0x13016c) low bit 0: the epilogue 0x650a4 returns -1 and the
             flags slot keeps 0x22 (else 0x65094-0x6509c clears MAP_ANONYMOUS and the model answers unmodeled)
     0x642ec a3 := 0x22, a4 := -1, a2 := 3, a0 := 0, a1 := s2, a5 := 0; jal internal_mmap 0x62ba8:
             li a7,222; ecall (0x62bac); ret
     0x64308 s3 := x; internal_iserror(x, 0) 0x62b88 and internal_iserror(x, sp) after sw 0xaaaaaaaa, 0(sp):
             x < 2^64 - 4095, so bltu 0x62b90 is taken and nothing is stored; a0 := 0, bnez 0x6432c falls through
     0x64330 IncreaseTotalMmap(s2) 0x5ea8c: GOT 0x965c0 -> common_flags, mmap_limit_mb (0x1300f8) = 0, beqz 0x5ea98
             to ret 0x5eab4 (the amoadd 0x5eaa4 and the RawWrite + Die arm are not reached)
     0x64338 a0 := x; restore ra/s0/s1/s2/s3; addi sp,sp,48; ret
   Touched stack bytes: [sp - 104, sp) (MmapOrDie's 48: sw 0(sp), sw 4(sp), the five saves; GetNamedMappingFd's 56:
   its seven saves); the rest of GetNamedMappingFd's 272-byte frame is never read or written on this path.
   ReportMmapFailureAndDie 0x5f37c (the refused arm) spins after main (the self-loop j 0 at 0x5f3ac, in AB12.v:19's stops_more); the premises make every
   refusal spurious at the ecall (anon_node, YF05.v:151; srz_mmap_rw_ok, YA09.v:726; line 87 below), so the contract has no refused arm. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AD3h.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v AF0x AB1w.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK0v YK13 YA09 YG0b YF05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YK02 YL0a.
(* md_takes and md_room have one home, a Theorem Labs lane's lib/A/AD3d.v (a Theorem Labs lane's text, verbatim). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AD3d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The touched stack bytes below the entry sp (see the header). *)
Definition MOD_STK : Z := 104.

(* The cells MmapOrDie and its callees read: the cached page size through the GOT slot 0x987c8 (0x65224), and
   common_flags through the GOT slot 0x987d8 (GetNamedMappingFd 0x65f10, IncreaseTotalMmap 0x5fa18):
   decorate_proc_maps (common_flags + 0x104) has its low bit clear, mmap_limit_mb (common_flags + 0x90) is 0.
   The same text as a Theorem Labs lane's mnr_cells (lib/A/AD3d.v:121-129), with MNR_ / mnr_ renamed MOD_ / mod_. *)
Definition MOD_PSC_GOT : Z := 0x987c8.
Definition MOD_PSC : Z := 0x130220.
Definition MOD_CF_GOT : Z := 0x987d8.
Definition MOD_CF : Z := 0x1322a8.
Definition mod_cells (m : word -> option byte) : Prop :=
  val_mem tfibsegs m MOD_PSC_GOT 8 MOD_PSC /\ val_mem tfibsegs m MOD_PSC 8 4096 /\
  val_mem tfibsegs m MOD_CF_GOT 8 MOD_CF /\
  (exists f, val_mem tfibsegs m (MOD_CF + 0x104) 1 f /\ Z.land f 1 = 0) /\
  val_mem tfibsegs m (MOD_CF + 0x90) 8 0.

(* Room and budget for MmapOrDie's grant, in the walk-stable form (eager_used, A_bytes and vm_limit do not change
   along the instruction steps before the ecall: they only materialize, eager_used_wvb YK04.v:788-790, and W is fixed
   along the walk). The budget pays n twice: the grant of flags 0x22 is charged at the ecall
   (mmap_noreserve_backed_ok, LPS Sys/Mm/Mmap.v:1233-1236; eager_used grows by at most n), and the range is then
   exposed in the world by allow_expose (YG0b.v:421-427), which adds [x, x + n) to w_A. commit_expose (YG0b.v:91-102)
   would not grow w_A, but it needs that no page of [x, x + n) is lazy in the model, which no invariant of the core
   states. *)
Definition mod_room (W : world tfibsegs) (md : Model) (n : Z) : Prop :=
  md_room md n /\ eager_used md + A_bytes (w_A W) + 2 * n <= vm_limit (m_vmmaps md).

(* S8, MmapOrDie (0x65200): mod_contract, consumed by name in lib/A/AD3g.v (AD3g.v:12-13); against a plain callee contract it differs as follows, each forced by
   the model or the code:
   - plain SRr: with mod_room every mmap refusal is spurious (srz_mmap_rw_ok, YA09.v:726; anon_node, YF05.v:151), so there
     is no refused arm; raw_report (a2) is free (its copy in s0 is used only on the refused arm, 0x65304);
   - premises added: the touched stack window [sp - MOD_STK, sp) and the image [TFIB_IMG_LO, TFIB_IMG_END) (the
     cells read after the ecall) are taken in the model, so the grant does not overwrite them; the stack window lies
     above the image;
   - the world grows: w_A W' = (x, x + size) :: w_A W and w_H W' differs from w_H W only inside [x, x + size)
     (allow_expose), instead of w_H W' = w_H W;
   - in_app x size is not given (the model places the grant only by grant_ok_na_pin; a caller with the ASan ledger
     gets in_app from AFia.grant_facts); the post states grant_ok_na_pin md x size = true and 0 < x instead;
   - the model after the call is stated exactly: the grant's vm_maps entry, plus materialized pages. *)
Definition mod_contract : Prop :=
  forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (size : Z),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs in
  argZ regs 0 = size -> 0 < size -> YG0f.page_aligned size -> argZ regs 1 <> 0 ->
  YK0s.ret_ok (getr regs 1) ->
  mod_cells m -> mod_room W md size ->
  sp mod 16 = 0 -> TFIB_IMG_END <= sp - MOD_STK -> (forall a, sp - MOD_STK <= a < sp -> apresent H mem a) ->
  md_takes md (sp - MOD_STK, MOD_STK) -> md_takes md (TFIB_IMG_LO, TFIB_IMG_END - TFIB_IMG_LO) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_MmapOrDie) mem (seg_rom tfibsegs)) md)
    (fun W' c' => exists x regs' mem' md',
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
      (* W *)  w_A W' = (x, x + size) :: w_A W /\
               (forall a : word, ~ (x <= bv_unsigned a < x + size) -> w_H W' a = w_H W a) /\
      (* P1 *) getr regs' 10 = Z_to_bv 64 x /\ regs_preserved regs regs' /\
      (* P2 *) YG0f.page_aligned x /\ 0 < x /\
      (* P3 *) grant_ok_na_pin md (Z_to_bv 64 x) size = true /\
               Forall (fun q => zdisjoint (x, size) (bv_unsigned (fst q), bv_unsigned (snd q)))
                 (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) /\ x + size <= alloc_top (m_vmmaps md) /\
      (* P4 *) (forall i, 0 <= i < size -> apresent (w_H W') mem' (x + i) /\ aview tfibsegs (w_H W') mem' (x + i) = Some 0) /\
               md_takes md' (x, size) /\ (forall e, md_takes md e -> md_takes md' e) /\
               (exists mat, md' = with_vm_backing (m_vm_lazy md) mat (mmap_model (Z_to_bv 64 x) (Z_to_bv 64 size) md)) /\
      (* P5 *) (forall a : word, ~ (sp - MOD_STK <= bv_unsigned a < sp) -> ~ (x <= bv_unsigned a < x + size) -> mem' a = mem a) /\
               (forall a, apresent H mem a -> apresent (w_H W') mem' a) /\ same_io md md').

End g.

(* THE PROOF. Three pieces, each in the core's SRr form (Reusable/YA0n.v):
   1. 0x65200 to the ecall 0x63b34: one symbolic run (SRr_run_to_sh_gen, YA0p.v:39) from SSM0, whose atoms are sp,
      size (page aligned, 4096 <= size), name (<> 0) and the decorate_proc_maps byte (even); the engine decides every
      branch on the way (GetPageSize skipped, IsPowerOfTwo, name <> 0, the decorate_proc_maps low bit) from those
      facts and the literal cells, and reaches the ecall with a0 = 0, a1 = size, a2 = 3, a3 = 0x22, a4 = -1, a5 = 0.
   2. The ecall: anon_node (YF05.v:151-167) lists only granting children, because md_room gives a grant and the
      budget gives mmap_noreserve_backed_ok (vm_backing_used_le, YA09.v:90-94); SRr_node (YA0n.v:106) consumes the
      node; each child's AI is AI_transport (YA0i.v:80) with mod_eager_used_mmap_le. The child's world is then
      wallow W x (x + size) (allow_expose, YG0b.v:421-427, which the second n of the budget pays), and the walk
      resumes with a fresh atom for x (st_ok_resume_atom, YP03.v:397); the stack window and the image cells keep
      their values because md_takes puts them apart from the grant (mod_takes_apart).
   3. 0x63b38 to the ret 0x652dc: one symbolic run (internal_iserror twice: x < 2^64 - 4095 from MOD_XF, so no
      store; IncreaseTotalMmap: mmap_limit_mb = 0, so no amoadd), then SRr_ret_at (YA0o.v:336).
   TAKEN FROM: the entry / run / return pattern of the core's tfib_ialloc_ok (A/AFfg.v:33-96); the ecall node and the
   world growth of the core's nodeS (A/AFjs.v:515-642); everything else is new (no donor). *)
(* ---- The decode table and the symbolic states (closed: every vm_compute below has no Section variable). ---- *)
Definition tfibtbl_mod_build : ctable := build_table tfibsegs 0x65200 67%nat (build_table tfibsegs 0x65edc 131%nat
  (build_table tfibsegs 0x63b10 11%nat (build_table tfibsegs 0x5fa14 17%nat TEmpty))).
Definition tfibtbl_mod : ctable := Eval vm_compute in tfibtbl_mod_build.
Lemma tfibtbl_mod_eq : tfibtbl_mod = tfibtbl_mod_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_mod). Qed.
Lemma tfibtbl_mod_ok : table_ok tfibsegs tfibtbl_mod.
Proof. rewrite tfibtbl_mod_eq. unfold tfibtbl_mod_build. do 3 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.

Definition mod_aDPM : nat := 32.
Definition mod_aX : nat := 33.
Definition MOD_FF : facts := mkFacts
  [ (2%nat, mkAF (TFIB_IMG_END + MOD_STK) (2 ^ 64 - 16) 4);
    (10%nat, mkAF 4096 (2 ^ 64 - 4096) 12);
    (11%nat, mkAF 1 (2 ^ 64 - 1) 0);
    (mod_aDPM, mkAF 0 254 1) ] [] [].
Definition mod_lit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition rMSTK : YP09.region := YP09.mkRegion (Some 2%nat) (- MOD_STK) 0 (- MOD_STK) 0 [].
Definition rMPSP : YP09.region := mod_lit8 MOD_PSC_GOT MOD_PSC.
Definition rMPS : YP09.region := mod_lit8 MOD_PSC 4096.
Definition rMCFG : YP09.region := mod_lit8 MOD_CF_GOT MOD_CF.
Definition rMDPM : YP09.region :=
  YP09.mkRegion None (MOD_CF + 0x104) (MOD_CF + 0x105) 0 0 [YP09.mkChunk (MOD_CF + 0x104) (CVal 1 (SOff mod_aDPM 0))].
Definition rMLIM : YP09.region := mod_lit8 (MOD_CF + 0x90) 0.
Definition SSM0 : sstate := mkSS 0x65200 sr_atoms [rMSTK; rMPSP; rMPS; rMCFG; rMDPM; rMLIM] None MOD_FF.
Definition SSME : sstate := Eval vm_compute in fst (sym_run_toN_sh tfibsegs tfibtbl_mod FUEL 0x7ffffff0 SSM0).
Lemma SSM0_run : sym_run_toN_sh tfibsegs tfibtbl_mod FUEL 0x7ffffff0 SSM0 = (SSME, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma SSME_facts :
  ss_pc SSME = 0x63b34 /\ ss_resv SSME = None /\
  sr_get (ss_regs SSME) 17%bv = SLit 222 /\ sr_get (ss_regs SSME) 10%bv = SLit 0 /\ sr_get (ss_regs SSME) 11%bv = SOff 10 0 /\
  sr_get (ss_regs SSME) 12%bv = SLit 3 /\ sr_get (ss_regs SSME) 13%bv = SLit 34 /\
  sr_get (ss_regs SSME) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs SSME) 15%bv = SLit 0 /\
  ss_atoms_lt mod_aX SSME = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition MOD_XF : afact := mkAF 4096 (2 ^ 64 - 2 ^ 23) 12.
Definition SSMR : sstate := resume SSME (SOff mod_aX 0) (ss_mem SSME)
  (mkFacts ((mod_aX, MOD_XF) :: f_atoms (ss_facts SSME)) (f_conds (ss_facts SSME)) (f_alias (ss_facts SSME))).
Definition SSMF : sstate := Eval vm_compute in fst (sym_run_toN_sh tfibsegs tfibtbl_mod FUEL 0x652dc SSMR).
Lemma SSMR_run : sym_run_toN_sh tfibsegs tfibtbl_mod FUEL 0x652dc SSMR = (SSMF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma SSMF_facts :
  ss_pc SSMF = 0x652dc /\ ss_resv SSMF = None /\ clookup tfibtbl_mod (ss_pc SSMF) = Some RET_WORD_r /\
  sr_get (ss_regs SSMF) 10%bv = SOff mod_aX 0 /\ sr_get (ss_regs SSMF) 1%bv = SOff 1 0 /\
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs SSMF) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true /\
  ss_mem SSMR = ss_mem SSME.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition mod_rshape (r : YP09.region) : option nat * Z * Z * Z * Z :=
  (YP09.r_base r, YP09.r_lo r, YP09.r_hi r, YP09.r_wlo r, YP09.r_whi r).
Definition MOD_SHAPE : list (option nat * Z * Z * Z * Z) :=
  [(Some 2%nat, -104, 0, -104, 0); (None, 0x987c8, 0x987d0, 0, 0); (None, 0x130220, 0x130228, 0, 0);
   (None, 0x987d8, 0x987e0, 0, 0); (None, 0x1323ac, 0x1323ad, 0, 0); (None, 0x132338, 0x132340, 0, 0)].
Lemma mod_shapes : map mod_rshape (ss_mem SSM0) = MOD_SHAPE /\ map mod_rshape (ss_mem SSME) = MOD_SHAPE /\ map mod_rshape (ss_mem SSMF) = MOD_SHAPE.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma mod_shape_extent : forall rs E r x, map mod_rshape rs = MOD_SHAPE -> In r rs ->
  base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
  (bv_unsigned (ew E 2) - 104 <= x < bv_unsigned (ew E 2)) \/ (TFIB_IMG_LO <= x < TFIB_IMG_END).
Proof.
intros rs E r x Hm Hin Hx. apply (in_map mod_rshape) in Hin. rewrite Hm in Hin. unfold mod_rshape in Hin.
destruct r as [b lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_lo YP09.r_hi] in *.
unfold MOD_SHAPE in Hin. cbn [In] in Hin. unfold TFIB_IMG_LO, TFIB_IMG_END.
destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]; injection Hin; intros; subst; cbn [base_val] in Hx; lia.
Qed.
Lemma mod_shape_window : forall rs E x, map mod_rshape rs = MOD_SHAPE -> in_wrange E rs x ->
  bv_unsigned (ew E 2) - 104 <= x < bv_unsigned (ew E 2).
Proof.
intros rs E x Hm (r & Hin & Hx). apply (in_map mod_rshape) in Hin. rewrite Hm in Hin. unfold mod_rshape in Hin.
destruct r as [b lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in *.
unfold MOD_SHAPE in Hin. cbn [In] in Hin.
destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]; injection Hin; intros; subst; cbn [base_val] in Hx; lia.
Qed.
Lemma mod_stack_nth : forall rs, map mod_rshape rs = MOD_SHAPE -> exists r, nth_error rs 0 = Some r /\
  YP09.r_base r = Some 2%nat /\ YP09.r_wlo r = -104 /\ YP09.r_whi r = 0.
Proof.
intros [|r rs] Hm; [discriminate|]. exists r. split; [reflexivity|]. cbn [map] in Hm. unfold mod_rshape at 1 in Hm.
injection Hm; intros; repeat split; assumption.
Qed.

(* ---- Model facts. ---- *)
Lemma mod_maps_subtract_app : forall l1 l2 lo hi, maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a s] l1 IH]; intros l2 lo hi; cbn [app maps_subtract]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma mod_msa_app : forall cuts l1 l2,
  maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts.
Proof. induction cuts as [|[a n] cuts IH]; intros l1 l2; cbn [maps_subtract_all]; [reflexivity|]. rewrite mod_maps_subtract_app. apply IH. Qed.
Lemma mod_live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a s] l1 IH]; intros l2; cbn [app live_bytes]; [reflexivity|]. rewrite IH. lia. Qed.
Lemma mod_live_iv_subtract_le : forall a sz lo hi, lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
intros a sz lo hi Hlh. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract. cbv zeta.
destruct (Z.ltb_spec (bv_unsigned a) lo) as [L|L]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [R|R];
cbn [app live_bytes].
all: try (destruct (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)) as [[M1 M2]|[M1 M2]]; rewrite M2).
all: try (destruct (Z.max_spec (bv_unsigned a) hi) as [[N1 N2]|[N1 N2]]; rewrite N2).
all: rewrite ?unsigned_lit_small by lia; lia.
Qed.
Lemma mod_live_ms_le : forall l lo hi, lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
induction l as [|[a s] l IH]; intros lo hi Hlh; cbn [maps_subtract live_bytes]; [lia|].
rewrite mod_live_bytes_app. pose proof (mod_live_iv_subtract_le a s lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.
Lemma mod_live_msa_le : forall cuts l, live_bytes (maps_subtract_all l cuts) <= live_bytes l.
Proof.
induction cuts as [|[a n] cuts IH]; intros l; cbn [maps_subtract_all]; [lia|].
eapply Z.le_trans; [apply IH|]. apply mod_live_ms_le. pose proof (u64_range n). lia.
Qed.
Lemma mod_eager_used_mmap_le : forall a n m, eager_used (mmap_model a n m) <= eager_used m + bv_unsigned n.
Proof.
intros a n m. unfold eager_used, vm_backed_maps, mmap_model. rewrite YK0g.m_vmmaps_with_vmmaps, YK0g.m_vm_lazy_with_vmmaps.
cbn [vm_maps vm_noaccess].
change ((a, n) :: vm_maps (m_vmmaps m)) with ([(a, n)] ++ vm_maps (m_vmmaps m)).
rewrite !mod_msa_app, mod_live_bytes_app.
pose proof (mod_live_msa_le (m_vm_lazy m) (maps_subtract_all [(a, n)] (vm_noaccess (m_vmmaps m)))) as X1.
pose proof (mod_live_msa_le (vm_noaccess (m_vmmaps m)) [(a, n)]) as X2. cbn [live_bytes] in X2. lia.
Qed.
Lemma mod_grant_split : forall md (a : word) n, grant_ok_na_pin md a n = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top (m_vmmaps md) /\
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a (Z_to_bv 64 n) = true.
Proof.
intros md a n Hg. unfold grant_ok_na_pin in Hg.
apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal. auto.
Qed.
Lemma mod_takes_apart : forall md e (a : word) n y,
  md_takes md e -> grant_ok_na_pin md a n = true -> 0 <= n < 2 ^ 64 -> n mod 4096 = 0 -> in_zr y e ->
  y < bv_unsigned a \/ bv_unsigned a + n <= y.
Proof.
intros md e a n y Ht Hg Hn Hnal Hy. destruct (mod_grant_split md a n Hg) as (Hal & _ & Htop & Hrf).
destruct Ht as [[Hp HE]|Ht].
- apply HE in Hy. apply Exists_exists in Hy as ([b s] & Hin & Hb). cbn [fst snd] in Hb.
  pose proof (YK13.region_free_In _ a (Z_to_bv 64 n) b s Hrf Hin) as D. rewrite unsigned_lit_small in D by lia. lia.
- pose proof (grant_end_page_floor (bv_unsigned a) n (alloc_top (m_vmmaps md)) Hal Hnal Htop) as Hpf.
  unfold in_zr in Hy. lia.
Qed.
Lemma mod_hcut_out : forall (Hh : word -> bool) lo hi (a : word), ~ (lo <= bv_unsigned a < hi) -> Hcut Hh lo hi a = Hh a.
Proof.
intros Hh lo hi a Ha. unfold Hcut.
destruct (Z.leb_spec lo (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) hi); cbn [andb negb];
rewrite ?andb_true_r; try reflexivity; exfalso; lia.
Qed.
Lemma mod_val_mem1 : forall m a f, val_mem tfibsegs m a 1 f -> val_mem tfibsegs m a 1 (f mod 256).
Proof.
intros m a f H k Hk. rewrite (H k Hk). assert (k = 0%nat) by lia. subst k. do 2 f_equal.
unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite !Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma mod_model_shape : forall (m : Model) mat1 mat2 mat3 (a n : word) m2,
  m2 = mmap_model a n (with_vm_backing (m_vm_lazy m) mat1 m) ->
  with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy m2) mat2 m2)) mat3 (with_vm_backing (m_vm_lazy m2) mat2 m2)
  = with_vm_backing (m_vm_lazy m) mat3 (mmap_model a n m).
Proof. intros m mat1 mat2 mat3 a n m2 ->. reflexivity. Qed.
Lemma mod_vmmaps_mmap : forall l X (a n : word) (m : Model),
  vm_maps (m_vmmaps (with_vm_backing l X (mmap_model a n m))) = (a, n) :: vm_maps (m_vmmaps m) /\
  vm_reserved (m_vmmaps (with_vm_backing l X (mmap_model a n m))) = vm_reserved (m_vmmaps m) /\
  alloc_top (m_vmmaps (with_vm_backing l X (mmap_model a n m))) = alloc_top (m_vmmaps m).
Proof. intros. repeat split; reflexivity. Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem mod_holds : mod_contract.
Proof.
unfold mod_contract. intros W regs mem md size. cbv zeta.
intros Hsz Hpos Hal Hname Hra HC HROOM Hsp16 HspLo HPRES HTS HTI.
pose proof Hwx_tfa as Hwx.
unfold spZ, argZ in *.
pose proof (u64_range (getr regs 2)) as Usp.
set (sp := bv_unsigned (getr regs 2)) in *.
assert (SPH : sp <= 2 ^ 64 - 16).
{ clear - Hsp16 Usp. pose proof (Z.div_mod sp 16 ltac:(lia)) as D. rewrite Hsp16 in D. set (q := sp / 16) in D. clearbody q. lia. }
assert (SPL : 0x5f5000 + 104 <= sp) by (clear - HspLo; unfold TFIB_IMG_END, MOD_STK in HspLo; lia).
destruct HC as (C1 & C2 & C3 & (f & C4 & C5) & C6).
destruct HROOM as ((g & Hg1 & Hg2 & Hg3 & Hg4) & HB).
pose proof (alloc_top_room (m_vmmaps md)) as ATR. unfold two_pow_64, stack_max_size in ATR.
set (fb := f mod 256).
assert (Hfb : 0 <= fb <= 254 /\ fb mod 2 = 0).
{ subst fb. assert (F2 : f mod 2 = 0).
  { pose proof (Z.land_ones f 1 ltac:(lia)) as X. change (Z.ones 1) with 1 in X. change (2 ^ 1) with 2 in X. rewrite <- X. exact C5. }
  assert (F3 : (f mod 256) mod 2 = 0) by (rewrite Z.mod_mod_divide; [exact F2 | exists 128; reflexivity]).
  pose proof (Z.mod_pos_bound f 256 ltac:(lia)) as B. pose proof (Z.div_mod (f mod 256) 2 ltac:(lia)) as D. rewrite F3 in D.
  split; [|exact F3]. clear - B D. set (y := f mod 256) in *. set (q := y / 2) in *. clearbody q y. lia. }
pose proof (mod_val_mem1 _ _ _ C4) as C4'. fold fb in C4'.
set (E0 := Ereg regs [Z_to_bv 64 fb]).
assert (E2 : ew E0 2 = getr regs 2) by exact (ew_Ereg_nat regs [Z_to_bv 64 fb] 2 2%bv eq_refl).
assert (E1 : ew E0 1 = getr regs 1) by exact (ew_Ereg_nat regs [Z_to_bv 64 fb] 1 1%bv eq_refl).
assert (E10 : bv_unsigned (ew E0 10) = size) by (rewrite <- Hsz; f_equal; exact (ew_Ereg_nat regs [Z_to_bv 64 fb] 10 _ eq_refl)).
assert (E11 : bv_unsigned (ew E0 11) <> 0) by (pose proof (ew_Ereg_nat regs [Z_to_bv 64 fb] 11 (Z_to_bv 5 (10 + 1)) eq_refl) as X; fold E0 in X; rewrite X; exact Hname).
assert (E32 : ew E0 mod_aDPM = Z_to_bv 64 fb) by reflexivity.
pose proof (u64_range (ew E0 11)) as U11.
assert (SZ : 4096 <= size /\ size + 2 ^ 23 < 2 ^ 64 /\ size mod 4096 = 0).
{ unfold YG0f.page_aligned in Hal. split; [|split; [lia | exact Hal]]. clear - Hal Hpos.
  pose proof (Z.div_mod size 4096 ltac:(lia)) as D. rewrite Hal in D. set (q := size / 4096) in D. clearbody q. lia. }
assert (HS : st_ok tfibsegs E0 SSM0 (restrict (w_H W) (mkst regs (Z_to_bv 64 tfib_A_MmapOrDie) mem (seg_rom tfibsegs)))).
{ unfold SSM0, tfib_A_MmapOrDie. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [| | | | | | apply Forall_nil].
    + apply (region_ok_stack tfibsegs E0 _ 2 sp (- MOD_STK)); [rewrite E2; reflexivity | unfold MOD_STK; lia | lia |].
      intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, MOD_STK in *; lia | apply HPRES; exact Ha].
    + unfold rMPSP, mod_lit8, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold MOD_PSC_GOT; lia|]. split; [unfold MOD_PSC_GOT; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | unfold MOD_PSC; cbn; lia | cbn; lia | rewrite Z.add_0_l; exact C1].
    + unfold rMPS, mod_lit8, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold MOD_PSC; lia|]. split; [unfold MOD_PSC; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact C2].
    + unfold rMCFG, mod_lit8, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold MOD_CF_GOT; lia|]. split; [unfold MOD_CF_GOT; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | unfold MOD_CF; cbn; lia | cbn; lia | rewrite Z.add_0_l; exact C3].
    + unfold rMDPM, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold MOD_CF; lia|]. split; [unfold MOD_CF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val tfibsegs E0 _ _ _ 1 _ fb);
      [cbn [sv_denot]; rewrite E32, (unsigned_lit_small fb), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact C4'].
    + unfold rMLIM, mod_lit8, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold MOD_CF; lia|]. split; [unfold MOD_CF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact C6].
  - apply pairwise_disjoint_of_extents. fold E0.
    unfold rMSTK, rMPSP, rMPS, rMCFG, rMDPM, rMLIM, mod_lit8, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2. fold sp. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold MOD_STK, MOD_PSC_GOT, MOD_PSC, MOD_CF_GOT, MOD_CF, TFIB_IMG_END in *. repeat split; lia.
  - fold E0. split; [|split; exact I]. cbn [MOD_FF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E32, (unsigned_lit_small fb) by lia. fold sp. rewrite E10.
    unfold MOD_STK, TFIB_IMG_END in *.
    repeat split; try lia. all: first [ exact SPH | change (2 ^ 4) with 16; exact Hsp16 | change (2 ^ 12) with 4096; exact (proj2 (proj2 SZ))
      | change (2 ^ 0) with 1; apply Z.mod_1_r | change (2 ^ 1) with 2; exact (proj2 Hfb) ]. }
(* ---- entry to the ecall at 0x63b34 (internal_mmap) ---- *)
eapply (SRr_run_to_sh_gen tfibsegs tfibtbl_mod tfibtbl_mod_ok Hwx W FUEL 0x7ffffff0 E0 SSM0 SSME RS_ecall _ _ _ HS SSM0_run).
cbv beta iota. intros ms1 mat1 HS1 HF1 _. cbn [ms_mem mkst] in HF1.
pose proof SSME_facts as (Epc & Eresv & R17s & R10s & R11s & R12s & R13s & R14s & R15s & Eat).
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E0 SSME ms1 HS1 Eresv) as (regs1 & mem1 & Hms1 & Hregs1 & Hmem1 & HG1).
rewrite Epc in Hms1. subst ms1. unfold YP0n.pend_at in HF1. cbn [ms_mem] in HF1. clear HS1.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
apply SRr_use_AI. intros HAI1. cbn [cfg_model] in HAI1.
assert (R17 : getr regs1 17%bv = Z_to_bv 64 222) by (rewrite Hregs1, R17s; reflexivity).
assert (R10 : getr regs1 10%bv = Z_to_bv 64 0) by (rewrite Hregs1, R10s; reflexivity).
assert (R11 : getr regs1 11%bv = Z_to_bv 64 size) by (rewrite Hregs1, R11s; cbn [sv_denot]; rewrite E10, Z.add_0_r; reflexivity).
assert (R12 : getr regs1 12%bv = Z_to_bv 64 3) by (rewrite Hregs1, R12s; reflexivity).
assert (R13 : getr regs1 13%bv = Z_to_bv 64 34) by (rewrite Hregs1, R13s; reflexivity).
assert (R14 : getr regs1 14%bv = Z_to_bv 64 (-1)) by (rewrite Hregs1, R14s; cbn [sv_denot]; apply bv_eq; reflexivity).
assert (R15 : getr regs1 15%bv = Z_to_bv 64 0) by (rewrite Hregs1, R15s; reflexivity).
assert (PRU : page_round_up_Z size = size) by (apply YK02.page_round_up_Z_aligned; [lia | unfold page_size; exact (proj2 (proj2 SZ))]).
assert (GEX : exists a, grant_ok_na_pin md1 a (page_round_up_Z size) = true).
{ rewrite PRU. exists (Z_to_bv 64 g). unfold grant_ok_na_pin. change (m_vmmaps md1) with (m_vmmaps md).
  rewrite (unsigned_lit_small g) by lia. unfold page_size. rewrite Hg4.
  apply andb_true_intro; split; [|reflexivity]. apply andb_true_intro; split; [apply andb_true_intro; split|].
  - apply Z.eqb_eq. exact Hg1.
  - apply Z.ltb_lt. exact Hg2.
  - apply Z.leb_le. exact Hg3. }
assert (EU1 : eager_used md1 = eager_used md) by apply eager_used_wvb.
assert (BOK : mmap_noreserve_backed_ok (Z_to_bv 64 34) md1 (page_round_up_Z size) = true).
{ rewrite PRU. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22. apply Z.leb_le.
  pose proof (YA09.vm_backing_used_le (w_A W) md1 (AI_MInv tfibsegs _ _ _ HAI1) (w_Awf W)) as VB.
  change (vm_limit (m_vmmaps md1)) with (vm_limit (m_vmmaps md)). clear - VB EU1 HB SZ. lia. }
destruct (anon_node tfibsegs regs1 (Z_to_bv 64 0x63b34) mem1 (seg_rom tfibsegs) md1 (Z_to_bv 64 34) size
  (AI_halted _ _ _ _ HAI1) R17 R10 R11 ltac:(lia) R12 R13 mmap_flags_core_22 R14 R15 GEX BOK)
  as (I & nx & bit & ga & i0 & NODE & _ & OUT).
assert (AIg : forall a : word, grant_ok_na_pin md1 a size = true ->
  AI tfibsegs (w_H W) (w_A W) (mmap_model a (Z_to_bv 64 size) md1) /\
  eager_used (mmap_model a (Z_to_bv 64 size) md1) <= eager_used md + size).
{ intros a Ha. pose proof (mod_eager_used_mmap_le a (Z_to_bv 64 size) md1) as EG. rewrite (unsigned_lit_small size) in EG by lia.
  rewrite EU1 in EG. split; [|exact EG].
  apply (AI_transport tfibsegs _ _ md1); [exact HAI1 | reflexivity | reflexivity | exact (AI_halted _ _ _ _ HAI1) |].
  change (vm_limit (m_vmmaps (mmap_model a (Z_to_bv 64 size) md1))) with (vm_limit (m_vmmaps md)). clear - EG HB SZ. lia. }
apply (SRr_node tfibsegs W _ I nx i0 _ NODE).
{ intros i _. destruct (OUT i) as (md_i & _ & _ & _ & Hg_i & NX_i & MD_i). rewrite NX_i. cbn [cfg_model]. rewrite MD_i.
  rewrite PRU in Hg_i |- *. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). exact (proj1 (AIg _ Hg_i)). }
intros i. destruct (OUT i) as (md_i & _ & _ & _ & Hg_i & NX_i & MD_i). rewrite NX_i. clear NX_i NODE OUT.
rewrite PRU in Hg_i, MD_i |- *. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22) in MD_i. subst md_i.
set (a := ga i) in *. set (A := bv_unsigned a).
assert (Hg0 : grant_ok_na_pin md a size = true) by exact Hg_i.
destruct (mod_grant_split md a size Hg0) as (GA1 & GA2 & GA3 & GA4). fold A in GA1, GA2, GA3.
pose proof (u64_range a) as UA. fold A in UA.
destruct (AIg a Hg_i) as [HAI2 EG2].
set (md2 := mmap_model a (Z_to_bv 64 size) md1) in *.
assert (AL1 : A <= A + size) by lia.
assert (AL2 : A mod page_size = 0) by (unfold page_size; exact GA1).
assert (AL3 : (A + size) mod page_size = 0).
{ unfold page_size. rewrite Z.add_mod by lia. rewrite GA1, (proj2 (proj2 SZ)). reflexivity. }
destruct (allow_expose tfibsegs W md2 A (A + size) AL1 AL2 AL3 HAI2) as (LE3 & WA3 & AB3 & VIS3 & MON3 & AI3).
{ change (vm_limit (m_vmmaps md2)) with (vm_limit (m_vmmaps md)). clear - EG2 HB SZ. lia. }
set (W3 := wallow tfibsegs W A (A + size) AL1 AL2 AL3) in *.
eapply (SRr_world_le tfibsegs W W3); [exact LE3 | intros _; exact AI3 |].
(* ---- the stack window and the image cells are apart from the grant ---- *)
assert (STK_OUT : forall y, sp - MOD_STK <= y < sp -> y < A \/ A + size <= y).
{ intros y Hy. apply (mod_takes_apart md _ a size y HTS Hg0 ltac:(lia) (proj2 (proj2 SZ))). unfold in_zr. cbn [fst snd]. lia. }
assert (IMG_OUT : forall y, TFIB_IMG_LO <= y < TFIB_IMG_END -> y < A \/ A + size <= y).
{ intros y Hy. apply (mod_takes_apart md _ a size y HTI Hg0 ltac:(lia) (proj2 (proj2 SZ))). unfold in_zr. cbn [fst snd]. lia. }
assert (A4K : 4096 <= A) by (clear - GA1 GA2; pose proof (Z.div_mod A 4096 ltac:(lia)) as D; rewrite GA1 in D; set (q := A / 4096) in D; clearbody q; lia).
assert (ATOP : A + size + 2 ^ 23 < 2 ^ 64) by (clear - GA3 ATR; lia).
set (E3 := ewset E0 mod_aX a).
assert (E3_2 : bv_unsigned (ew E3 2) = sp) by (unfold E3; rewrite ew_ewset_other by (unfold mod_aX; lia); rewrite E2; reflexivity).
assert (HS2 : st_ok tfibsegs E3 SSMR (restrict (w_H W3) (mkst (regupd regs1 10 a) (v_addi (Z_to_bv 64 0x63b34) 4)
  (zfill a (Z_to_bv 64 size) mem1) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. rewrite <- Epc. unfold SSMR, E3.
  apply (st_ok_resume_atom tfibsegs mod_aX MOD_XF E0 SSME regs1 _ a Hregs1); [ | exact HG1 | exact Eat | cbn [af_lo af_hi MOD_XF]; clear - A4K ATOP SZ; lia
    | cbn [af_al2 MOD_XF]; lia | cbn [af_al2 MOD_XF]; change (2 ^ 12) with 4096; exact GA1 ].
  apply (mem_ok_mrestrict_hsub tfibsegs (w_H W) (w_H W3) E0 _ _ (w_Hoff W) LE3).
  apply (YL0a.mem_ok_ext_same tfibsegs E0 (mrestrict (w_H W) mem1)); [exact Hmem1|].
  intros r x Hr Hx. pose proof (mod_shape_extent _ E0 r x (proj1 (proj2 mod_shapes)) Hr Hx) as SX. rewrite E2 in SX. fold sp in SX.
  assert (X64 : 0 <= x < 2 ^ 64) by (unfold TFIB_IMG_LO, TFIB_IMG_END in SX; lia).
  unfold mrestrict. destruct (w_H W (Z_to_bv 64 x)); [reflexivity|].
  apply zfill_out. rewrite (unsigned_lit_small x), (unsigned_lit_small size) by lia. fold A.
  destruct SX as [SX|SX]; [apply STK_OUT; unfold MOD_STK; lia | apply IMG_OUT; exact SX]. }
(* ---- 0x63b38 (internal_mmap's ret) to MmapOrDie's ret at 0x652dc ---- *)
eapply (SRr_run_to_sh_gen tfibsegs tfibtbl_mod tfibtbl_mod_ok Hwx W3 FUEL 0x652dc E3 SSMR SSMF RS_running _ _ _ HS2 SSMR_run).
cbv beta iota. intros ms2 mat2 HS3 HF2 _. cbn [ms_mem mkst] in HF2. clear HS2.
pose proof SSMF_facts as (Fpc & Fresv & Fret & F10 & F1 & Fcs & Fmem).
eapply (SRr_ret_at tfibsegs tfibtbl_mod tfibtbl_mod_ok Hwx W3 E3 SSMF ms2 _ _ HS3 Fresv Fret).
intros mat3.
assert (MEM1 : forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> mem1 x = mem x).
{ intros x Hx. apply HF1. intros Hw. apply Hx. pose proof (mod_shape_window _ E0 _ (proj1 mod_shapes) Hw) as W'.
  rewrite E2 in W'. fold sp in W'. unfold MOD_STK. lia. }
assert (MEM2 : forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ms_mem ms2 x = zfill a (Z_to_bv 64 size) mem1 x).
{ intros x Hx. apply HF2. intros Hw. apply Hx. rewrite Fmem in Hw. pose proof (mod_shape_window _ E3 _ (proj1 (proj2 mod_shapes)) Hw) as W'.
  rewrite E3_2 in W'. unfold MOD_STK. lia. }
assert (STK_NOT : forall x : word, A <= bv_unsigned x < A + size -> ~ (sp - MOD_STK <= bv_unsigned x < sp)).
{ intros x Hx Hs. destruct (STK_OUT _ Hs); lia. }
assert (ZERO : forall x : word, A <= bv_unsigned x < A + size -> ms_mem ms2 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (MEM2 x (STK_NOT x Hx)). apply zfill_in. rewrite (unsigned_lit_small size) by lia. exact Hx. }
assert (R1F : getr (ms_regs ms2) 1%bv = getr regs 1%bv).
{ rewrite (st_ok_reg_denot (w_H W3) E3 SSMF ms2 1%bv HS3), F1. cbn [sv_denot]. unfold E3.
  rewrite ew_ewset_other by (unfold mod_aX; lia). rewrite E1, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (R10F : getr (ms_regs ms2) 10%bv = Z_to_bv 64 A).
{ rewrite (st_ok_reg_denot (w_H W3) E3 SSMF ms2 10%bv HS3), F10. cbn [sv_denot]. unfold E3.
  rewrite ew_ewset_same, Z.add_0_r. reflexivity. }
assert (MDEQ : with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat2 md2)) mat3 (with_vm_backing (m_vm_lazy md2) mat2 md2)
  = with_vm_backing (m_vm_lazy md) mat3 (mmap_model a (Z_to_bv 64 size) md)) by exact (mod_model_shape md mat1 mat2 mat3 a (Z_to_bv 64 size) md2 eq_refl).
rewrite MDEQ. clear MDEQ.
pose proof (mod_vmmaps_mmap (m_vm_lazy md) mat3 a (Z_to_bv 64 size) md) as (VM1 & VM2 & VM3).
cbv beta.
exists A, (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md) mat3 (mmap_model a (Z_to_bv 64 size) md)).
split. { rewrite R1F. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { exact WA3. }
split. { intros x Hx. unfold W3, wallow. cbn [w_H]. apply mod_hcut_out. exact Hx. }
split. { exact R10F. }
split. { apply (regs_preserved_of_st_ok tfibsegs E3 SSMF (restrict (w_H W3) ms2) regs [Z_to_bv 64 fb] HS3); [| exact Fcs].
  apply (env_agree_le 33 32 E0 E3); [lia | exact (env_agree_ewset E0 mod_aX a)]. }
split. { unfold YG0f.page_aligned. exact GA1. }
split. { exact GA2. }
split. { unfold A. rewrite Z_to_bv_bv_unsigned. exact Hg0. }
split. { apply Forall_forall. intros [b s] Hin. pose proof (YK13.region_free_In _ a (Z_to_bv 64 size) b s GA4 Hin) as D.
  rewrite (unsigned_lit_small size) in D by lia. fold A in D. unfold zdisjoint. cbn [fst snd]. lia. }
split. { exact GA3. }
split. { intros k Hk. assert (XK : A <= bv_unsigned (Z_to_bv 64 (A + k)) < A + size) by (rewrite unsigned_lit_small by lia; lia).
  pose proof (ZERO _ XK) as Z0. pose proof (VIS3 _ XK) as V0. split.
  - split; [exact V0 | exists (Z_to_bv 8 0); exact Z0].
  - unfold aview, mbyte, mrestrict. rewrite V0, Z0. reflexivity. }
split. { left. split; [cbn [snd]; lia|]. intros y Hy. unfold in_zr in Hy. cbn [fst snd] in Hy. rewrite VM1, VM2.
  apply Exists_app. right. apply Exists_cons_hd. cbn [fst snd]. rewrite (unsigned_lit_small size) by lia. fold A. lia. }
split. { intros e [[Hp HE]|Ht].
  - left. split; [exact Hp|]. intros y Hy. specialize (HE y Hy). rewrite VM1, VM2.
    apply Exists_app in HE as [HE|HE]; apply Exists_app; [left; exact HE | right; apply Exists_cons_tl; exact HE].
  - right. rewrite VM3. exact Ht. }
split. { exists mat3. unfold A. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split. { intros x Hs Hg. rewrite (MEM2 x Hs). rewrite zfill_out. 2: { rewrite (unsigned_lit_small size) by lia. fold A. lia. }
  exact (MEM1 x Hs). }
split. { intros y [Hy1 [b Hb]]. unfold apresent. set (w := Z_to_bv 64 y) in *. pose proof (u64_range w) as Uw.
  assert (Ew : Z_to_bv 64 (bv_unsigned w) = w) by apply Z_to_bv_bv_unsigned.
  destruct (Z.lt_ge_cases (bv_unsigned w) (sp - MOD_STK)) as [L1|L1];
  [| destruct (Z.lt_ge_cases (bv_unsigned w) sp) as [L2|L2]].
  2: { destruct (mod_stack_nth _ (proj2 (proj2 mod_shapes))) as (r & Hr & Rb & Rl & Rh).
       assert (WR : base_val E3 (YP09.r_base r) + YP09.r_wlo r <= bv_unsigned w < base_val E3 (YP09.r_base r) + YP09.r_whi r)
         by (rewrite Rb, Rl, Rh; cbn [base_val]; rewrite E3_2; unfold MOD_STK in *; lia).
       pose proof (st_ok_window_apresent (w_H W3) E3 SSMF ms2 0 r (bv_unsigned w) HS3 Hr WR
         ltac:(unfold TFIB_IMG_END, MOD_STK in *; lia)) as P.
       unfold apresent in P |- *. rewrite Ew in P. fold w. exact P. }
  all: assert (NS : ~ (sp - MOD_STK <= bv_unsigned w < sp)) by lia.
  all: destruct (Z.lt_ge_cases (bv_unsigned w) A) as [G1|G1]; [| destruct (Z.lt_ge_cases (bv_unsigned w) (A + size)) as [G2|G2]].
  all: try (split; [exact (VIS3 w ltac:(lia)) | exists (Z_to_bv 8 0); exact (ZERO w ltac:(lia))]).
  all: split; [exact (MON3 w Hy1) | exists b; rewrite (MEM2 w NS), zfill_out, (MEM1 w NS); [exact Hb|];
    rewrite (unsigned_lit_small size) by lia; fold A; lia]. }
repeat split; reflexivity.
Qed.
End p.
