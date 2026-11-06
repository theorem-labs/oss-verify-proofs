(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 616 of its 728 lines of code are new or changed and 1195 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8, listing offset AF_reac_served_mark = 0x73dc) on image A: the HEAD of its
   walk, from the contract's entry (+0x00) to THE MID CUT (+0x1b4 `beqz s6`) of lib/A/Prog/reac_served_markDefs.v.
   Listing (internal path) (internal record, sha256 5943815fc488).

   The code of the segment:
     +0x00..+0x38  the 128-byte machine frame, `sd zero, 0(sp)`, the twelve saves (ra at sp - 8, s0 .. s10 below it),
                   s0 := the entry sp                                                       (run 1, token engine)
     +0x3c..+0x40  `andi sp, sp, -0x20`: the realigned stack pointer sp1, s1 := sp1
     +0x44..+0x60  s4 := a1 (the name); the side-stack switch cell (.got 0xa1a28 -> 0xaa440, 1 by AR's const law)
                   and the shadow base (.got 0xa19d0 -> 0xaa438 -> SHADOW_OFF) into s10; s6 := a0 (the marks block)
     +0x64         `beqz a2`: the switch cell is 1, the engine decides it (the real-stack arm is not reached)
     +0x68..+0x6c  a0 := 0x1a0; jal frame_alloc_3 (0x3dc18): LinkWalkSide.v aj_gx_stack_malloc_at over ASM3, with
                   the class-3 room from aside_room's (3, 2)
     +0x70..+0x80  s3 := s9 := F; `bnez s3` is taken (F >= 4096 from the post)              (run 2, plain engine)
     +0xa0         `sd s9, 0x18(s1)`: the frame address in the machine frame
     +0xa4..+0xcc  F's header: the magic 0x41b58ab3 at F, the descriptor 0x14868 at F + 8, the pc 0x895a8 at F + 16
     +0xd0..+0x1ac the shadow of F's redzones and buffers into SH = SHADOW_OFF + F / 8 .. SH + 0x33
     +0x1b0        s5 := -22
   The MID cut's state `srm_gi_mid` (srm_base with X = no write-set byte) is built from the two runs and the
   frame_alloc_3 post: the journal with this call's frame on top of `own`, the side stack and the frame witness S1
   (the post's state), the registers, the twelve saved words (the machine frame's region), the flag-address word at
   F + 504 (the post's, kept by run 2), the presence of F and of its shadow (AR's frame law), the kept clause (the
   entry's window plus F's bytes and shadow through `aside_rng`), the descriptors and the file system, the read-only
   image (akept's image clause; the relro window lies in the image), and the rounding mode.

   Section hypotheses: LAWS (AR_laws), HV (LinkVals), TL (PALib), ASM3 (frame_alloc_3's contract, discharged by
   lib/A/Rt/StackSideInst.v link_stack_malloc_3), HSM3 (frame_alloc_3's entry in the code record: lib/A/AF0l.v
   Tfib_code maps class 3 to 0x3dc18, and lv_sigma gives pa_sigma LS___asan_stack_malloc_3 = 0x3dc18), HSEGS
   (pa_segs = tfibsegs, the link PAImg instance by reflexivity: the relro window [PCAP_RLO, PCAP_RHI) is inside the
   image, lib/A/Prog/PcapRelroA.v).

   Proves no function (kind: segment lemma of reac_served_mark's walk: the contract entry to the MID cut). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_mark_c reac_served_markDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelroA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   The symbolic data (closed: every definition below computes)
   ========================================================================== *)

Definition SRH_SB : Z := 0x7fff8000.
Lemma SRH_SB_eq : SRH_SB = SHADOW_OFF. Proof. reflexivity. Qed.
Definition SRH_Bx : sv := SOff 32 0.
Definition SRH_span : Z * Z := (SRH_SB, SRH_SB + 2 ^ 44 - 1).
Definition SRH_extra : list word := [Z_to_bv 64 SRH_SB].
(* the entry: the 128-byte machine frame, the shadow-base GOT word and its cell, the side-stack switch GOT word
   and its cell (the same entry as reac_link_alias_read, whose prologue has this shape) *)
Definition srh_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0 [].
Definition srh_got : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 64) 0))].
Definition srh_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 64)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition srh_ugot : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 65) 0))].
Definition srh_ucell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 65)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition srh_regions : smem := [srh_stack; srh_got; srh_cell; srh_ugot; srh_ucell].
Definition srh_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SRH_SB SRH_SB 0)] [] [].
Definition srh_ss : sstate := mkSS AF_reac_served_mark sr_atoms srh_regions None srh_facts.

(* after the call: 44 = F (a0 after the call: the junk atoms of CLOB from 40), 60 = sp1, 62 = SH = SB + F / 8 *)
Definition srh_W1 : YP09.region := YP09.mkRegion (Some 60%nat) 24 32 24 32 [].
Definition srh_F : YP09.region := YP09.mkRegion (Some 44%nat) 0 24 0 24 [].
Definition srh_SH : YP09.region := YP09.mkRegion (Some 62%nat) 0 52 0 52 [].

(* the machine frame cut to the twelve saves, read-only from here *)
Definition srh_chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
  Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition srh_trim (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (-96) 0 0 0 (filter (srh_chunk_in (-96) 0) (YP09.r_chunks r)).
Definition srh_trim_first (rs : smem) : smem := match rs with r :: _ => [srh_trim r] | [] => [] end.

(* ==========================================================================
   Generic helpers (copied from lib/A/Prog/LinkWalkPi.v, which is not imported; renamed)
   ========================================================================== *)

Lemma srh_div8_of_mul64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.
Lemma srh_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma srh_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma srh_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite srh_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma srh_denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)) as Hle. pose proof (Z.div_pos (v + c) 32 ltac:(lia) ltac:(lia)) as Hp.
assert (HU : U E (SAlu ALU_AND (SOff n c) (SLit (-32))) = 32 * ((v + c) / 32)).
{ unfold U. rewrite (srh_denot_and_m32 E n v c Hn H0 H1 Hv). apply unsigned_lit_small. lia. }
rewrite HU. apply zcanon_id. unfold M64. lia.
Qed.
Lemma srh_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (pose proof (H 0 ltac:(lia)) as H0; rewrite Z.add_0_r in H0; exact H0).
rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)),
  (H 6 ltac:(lia)), (H 7 ltac:(lia)).
reflexivity.
Qed.
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma srh_ms_shape : forall segs (msx : machine_state) r pcv m,
  msx = mkst r pcv m (seg_rom segs) ->
  ms_resv msx = None /\ ms_svc_pending msx = None /\ ms_rom msx = seg_rom segs /\
  ms_fregs msx = fp_regs /\ ms_fcsr msx = fp_csr /\ ms_pc_val msx = pcv.
Proof. intros segs msx r pcv m H. repeat split; rewrite H; reflexivity. Qed.

Lemma srh_val_mem_of_rd32 : forall segs H mem a v,
  YG0n.rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros segs H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma srh_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma srh_ast_ok_set_reg : forall segs E ss ms (r : bv 5) e,
  st_ok segs E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
  st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms r e HS Hr0 He. apply st_ok_regs; [exact HS|].
intros rr. destruct (Z.eq_dec (bv_unsigned rr) (bv_unsigned r)) as [Heq|Hne].
- assert (rr = r) as -> by (apply bv_eq; exact Heq).
  rewrite sr_get_set_same by exact Hr0. rewrite He. apply (st_ok_reg segs E ss ms r HS).
- rewrite sr_get_set_other by (intros ->; apply Hne; reflexivity). reflexivity.
Qed.
Lemma srh_frame_al64 : forall segs B, AR_laws segs B -> forall ly S W mem md cid pos,
  AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
intros segs B LAWS ly S W mem md cid pos [M _] Hin.
destruct (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
End u.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable lsym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Lemma srh_pi_havoc_hi : forall k E ss ms ws,
  st_ok_pi SEGS VAL E ss ms -> ss_atoms_p (pband k (k + length ws)) ss = true ->
  st_ok_pi SEGS VAL (havoc E k ws) ss ms.
Proof.
intros k E ss ms ws HS Hat. unfold st_ok_pi in *.
eapply (st_ok_agree_p (pband k (k + length ws)) SEGS); [exact HS | | destruct ss; exact Hat].
apply env_agree_p_havoc. apply le_n.
Qed.
Lemma srh_pi_set_reg : forall E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms r e HS Hr He. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (srh_ast_ok_set_reg SEGS E _ ms r e HS Hr He). Qed.
Lemma srh_pi_add_alias : forall E ss ms e1 e2,
  st_ok_pi SEGS VAL E ss ms -> sv_denot E e1 = sv_denot E e2 ->
  st_ok_pi SEGS VAL E (set_facts ss (mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((e1, e2) :: f_alias (ss_facts ss)))) ms.
Proof. intros E ss ms e1 e2 HS He. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_add_alias SEGS E _ ms e1 e2 HS He). Qed.
Lemma srh_pi_region_nth : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.
End z.

(* tactics (LinkWalkPi.v's, renamed) *)
Ltac srh_prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* a register goal `getr (ms_regs m) r = _`, its left side replaced by the state's symbolic value of r *)
Ltac srh_st_reg HS :=
  lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H m) =>
      rewrite (st_ok_restrict_reg segs H E ss m r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e
    end end.
Ltac srh_pi_reg HS :=
  lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
    lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H m) =>
      rewrite (st_ok_pi_restrict_reg H E ss m r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned
    end end.
Ltac srh_subregion_tac :=
  unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
  let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
  first [exact Hc | solve [destruct Hc] | tauto].
Ltac srh_submem_to := repeat (first [apply submem_keep; [srh_subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac srh_norm_pi HS :=
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let v := eval vm_compute in ss in change ss with v in HS end.
Ltac srh_add_fact HS n f prf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_fact Ev ssx msx n f HS ltac:(prf)) as HS3; clear HS; rename HS3 into HS; srh_norm_pi HS end.
(* one saved word of the MID cut, `rdword rd (sp - 16 - 8 j) = Some (bv_unsigned (getr regs r))`, from SAVE *)
Ltac srh_save_tac SAVE regs :=
  lazymatch goal with |- rdword _ (spZ regs - 16 - 8 * ?jj) = Some (bv_unsigned (getr regs (Z_to_bv 5 ?rr))) =>
    let rv := eval vm_compute in rr in
    let rn := eval vm_compute in (Z.to_nat rv) in
    let ov := eval vm_compute in (- 16 - 8 * jj) in
    replace (spZ regs - 16 - 8 * jj) with (spZ regs + ov) by lia;
    change (Z_to_bv 5 rr) with (Z_to_bv 5 (Z.of_nat rn));
    exact (SAVE rn ov ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia))
  end.
(* the plain run to a stop offset, over ajournal_gx (LinkWalkSide.v paj_run_to_plain_x) *)
Ltac srh_run_to_plain RUNTOP HS HJ stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNTOP with
    | context [sym_run_toN_pi ?tpi _ _ _] =>
      let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "srh_run_to_plain: no img_env for" E end in
        eapply (RUNTOP W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ); clear Hrun
      end
    end
  end.

(* ==========================================================================
   The entry state, and the walk
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.
(* frame_alloc_3 (0x3dc18): lib/A/Rt/StackSideInst.v link_stack_malloc_3, at tfibsegs *)
Hypothesis ASM3 : astack_malloc_realizes pa_segs B 3.
(* its entry in the code record (lib/A/AF0l.v Tfib_code: class 3 -> 0x3dc18; lv_sigma: the listing's symbol) *)
Hypothesis HSM3 : pc_stack_malloc (as_code B) 3 = pa_sigma LS___asan_stack_malloc_3.
(* the one segment computation: the relro window lies in the image (the link PAImg instance: reflexivity) *)
Hypothesis HSEGS : pa_segs = tfibsegs.

Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let HBguar := pal_got_uar B TL.
Let HBuar := pal_uar_cell B TL.
Let errno_low := pal_env B TL.

Lemma srh_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.
Proof.
intros a Ha. rewrite HSEGS. destruct pcap_relro_in_image as (s & Hin & H1 & H2 & H3).
exists s. split; [exact Hin | lia].
Qed.

Lemma srh_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_SERVED_MARK_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs SRH_extra)) srh_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_reac_served_mark)) memc (seg_rom pa_segs))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJX Hal16 Hwlo Hwhi.
destruct HJX as (HSTK & HXO & (memS & HJ & Hag) & Hout).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : REAC_SERVED_MARK_AK = 9504) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (lv_obj HV 0%nat ltac:(unfold link_nobj; lia)) as V0.
pose proof (lv_obj HV 1%nat ltac:(unfold link_nobj; lia)) as V1.
pose proof (lv_obj HV 64%nat ltac:(unfold link_nobj; lia)) as V64.
pose proof (lv_obj HV 65%nat ltac:(unfold link_nobj; lia)) as V65.
cbv [link_obj] in V0, V1, V64, V65.
set (E := Eimg (Ereg regs SRH_extra)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs SRH_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SRH_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs SRH_extra 0)).
assert (EIMG : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBI : forall i, (i < 66)%nat -> base_val E (Some (A_OBJ i)) = pa_val (A_OBJ i)).
{ intros i Hi. cbn [base_val]. rewrite (EIMG i Hi). apply unsigned_lit_small.
  pose proof (pa_val_range (A_OBJ i)). lia. }
rewrite restrict_mkst_fx. unfold srh_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold srh_regions, srh_stack, srh_got, srh_cell, srh_ugot, srh_ucell.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable pa_segs). cbn [ms_mem restrict mkst]. apply Hpres. lia.
  + fold E. rewrite (VBI 1%nat ltac:(lia)).
    split; [rewrite V1; lia|]. split; [rewrite V1; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 64) 0) (pa_val (A_OBJ 64)));
      [ cbn [sv_denot]; rewrite (EIMG 64%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 64)); zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBI 64%nat ltac:(lia)).
    split; [rewrite V64; lia|]. split; [rewrite V64; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 64)) 0 8 (SOff 32 0) SRH_SB);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SRH_SB; zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VBI 0%nat ltac:(lia)).
    split; [rewrite V0; lia|]. split; [rewrite V0; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 0)) 0 8 (SOff (A_OBJ 65) 0) (pa_val (A_OBJ 65)));
      [ cbn [sv_denot]; rewrite (EIMG 65%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 65)); zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kguar).
  + fold E. rewrite (VBI 65%nat ltac:(lia)).
    split; [rewrite V65; lia|]. split; [rewrite V65; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 65)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (srh_val_mem_of_rd32 pa_segs (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold srh_regions, srh_stack, srh_got, srh_cell, srh_ugot, srh_ucell, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite !VBI by lia. cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite V0, V1, V64, V65.
  revert Hslo Hshi H47 Hceil C1a C1b C3 HK Hstk0 Hwlo Hwhi. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [srh_facts f_atoms atoms_ok]. split; [|split; [|exact I]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite Usp. change (2 ^ 4) with 16.
    revert Hal16 Hslo Hshi H47 Hceil C1a C1b C3 HK Hstk0 Hwlo Hwhi HSTK HXO. clear. intros.
    repeat split; lia.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite E32, unsigned_lit_small by (unfold SRH_SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.

(* THE HEAD: from the contract's entry to the MID cut. *)
Theorem srm_head : srm_mid_obl fx SK B -> reac_served_mark_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
intros HMID. apply (srm_shape SK B). intros cx HPREX HFRM.
pose proof HPREX as (HPRE & HRD & HP).
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
set (G := sm_G cx) in *. set (XO := sm_XO cx) in *. set (OUT := sm_OUT cx) in *.
set (STK := sm_STK cx) in *. set (sp0 := sm_sp0 cx) in *. set (FP := sm_FP cx) in *.
set (ly := sm_ly cx) in *. set (S := sm_S cx) in *. set (W0 := sm_W0 cx) in *.
set (mem0 := sm_mem0 cx) in *. set (md0 := sm_md0 cx) in *. set (own := sm_own cx) in *.
set (lyc := sm_lyc cx) in *. set (Sc := sm_Sc cx) in *. set (W := sm_W cx) in *.
set (memc := sm_memc cx) in *. set (mdc := sm_mdc cx) in *. set (k := sm_k cx) in *.
set (regs := sm_regs cx) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : REAC_SERVED_MARK_AK = 9504) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(lia) Hwhi)
  as (memS & _ & _ & _ & HSTK & HXO & _ & _ & _ & _ & Hceil & H47).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
assert (Hspc : alloc_ceiling + REAC_SERVED_MARK_AK <= spZ regs) by lia.
pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
  as Hpres0.
(* ---- the entry state ---- *)
pose proof (srh_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hwlo Hwhi) as HS.
remember (Eimg (Ereg regs SRH_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs SRH_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SRH_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs SRH_extra 0)).
assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  symmetry. apply Z.mod_small. lia. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
clear HEdef EL.
assert (SHOK : sh_ok pa_segs SRH_Bx (@nil shent) E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (HCFG : cfg_at pa_segs REAC_SERVED_MARK_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_reac_served_mark)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text HV). reflexivity. }
change (SRr pa_segs W (cfg_at pa_segs REAC_SERVED_MARK_A regs memc mdc) (srm_post fx SK B cx)).
rewrite HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNTOP := paj_run_to_plain_x SK B LAWS G HGok XO OUT).
(* ---- run 1: the prologue, the two GOT loads and the switch test, up to frame_alloc_3 (+0x6c) ---- *)
paj_run_tok RUN HS HJ SHOK SRH_span;
  [ unfold srh_ss, srh_regions, srh_stack, srh_got, srh_cell, srh_ugot, srh_ucell;
    apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp in Ha;
      left; split; [left; lia | lia]
    | repeat (apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia|]);
      apply awr_ok_x_nil ] |].
rename ms into msA.
pose proof HJ as HJA.
pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJA)
  as HpresA.
(* what run 1 kept: every byte outside the machine frame [sp - 128, sp) *)
assert (UN1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview pa_segs (w_H W) (ms_mem msA) a = aview pa_segs (w_H W) memc a).
{ apply (kept_of_frame (segs := pa_segs) E srh_regions (w_H W) memc (ms_mem msA)
    (fun a => spZ regs - 128 <= a < spZ regs) HFr).
  intros bb wlo whi a Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp in Hr; lia|]).
  destruct Hin. }
pmkst HS.
assert (R1 : getr (ms_regs msA) 1 = Z_to_bv 64 (pa_val A_TEXT + 29772)).
{ srh_st_reg HS. change (SOff 240 29772) with (SOff A_TEXT 29772). exact (codeptr_val E 29772 HEI). }
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
assert (Hsp1e : 32 * ((spZ regs + -128) / 32) = sp1) by (unfold sp1; f_equal; f_equal; lia).
destruct (srh_sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (R2 : getr (ms_regs msA) 2 = Z_to_bv 64 sp1).
{ srh_st_reg HS. rewrite (srh_denot_and_m32 E 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e.
  reflexivity. }
assert (R3 : getr (ms_regs msA) 3 = w64 (as_gp B)).
{ srh_st_reg HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EREG 3%nat ltac:(lia)).
  rewrite <- Hgp. f_equal; apply bv_eq; reflexivity. }
assert (R4 : getr (ms_regs msA) 4 = w64 (as_tp B)).
{ srh_st_reg HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EREG 4%nat ltac:(lia)).
  rewrite <- Htp. f_equal; apply bv_eq; reflexivity. }
assert (Rsp : spZ (ms_regs msA) = sp1) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hcnt : count_cid 3 (frames Sc) < fs_frames 3).
{ apply (aside_room_take Sc REAC_SERVED_MARK_ASIDE 3 2 Hside);
  [ unfold REAC_SERVED_MARK_ASIDE; cbn [In]; left; reflexivity | lia ]. }
(* the machine frame cut to the twelve saves (read-only from here); the GOT words and the cells are dropped *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (srh_trim_first rs) in
  pose proof (st_ok_submem pa_segs Ex ssx msx rs' HS ltac:(cbn [ss_mem setpc]; srh_submem_to)
    ltac:(vm_compute; reflexivity)) as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts setpc] in HS.
(* ---- frame_alloc_3(0x1a0): the class-3 frame (3, fpos) on top of own ---- *)
eapply SRr_bind.
{ eapply (aj_gx_stack_malloc_at SK pa_segs B LAWS Hsegs errno_low 3 ASM3 ltac:(lia)
    (pa_sigma LS___asan_stack_malloc_3) G XO OUT W (ms_regs msA) (ms_mem msA) STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc _ k _ HSM3 HJA).
  - rewrite Rsp. exact Hsp1al16.
  - rewrite Rsp. lia.
  - rewrite Rsp. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hcnt. }
cbv beta. intros W2 c2 _ (-> & S2 & regs1 & mem2 & md2 & fpos & -> & HJ2 & HP1 & Ha01 & Eab2 & Hfrs2 & Hnin2
  & Hnev2 & Hbb2 & Hfs2 & HF4096 & HFceil & Hz & Hflagw & HKEPT & Hsame2 & Hraw2).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((3, fpos) :: own) lyc S2 W mem2 md2 k
  HJ2) as HAR2.
set (F := frame_addr lyc 3 fpos) in *.
set (FL := flag_addr lyc 3 fpos) in *.
assert (Hin2 : In (3, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (srh_frame_al64 pa_segs B LAWS lyc S2 W mem2 md2 3 fpos HAR2 Hin2) as (HFa64 & _ & _).
change (fs_frame_bytes 3) with 512 in *.
destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 3 fpos HAR2 Hin2) as (_ & HFapp & HFpres & HFSpres).
change (fs_frame_bytes 3) with 512 in HFapp, HFpres, HFSpres. change (512 / 8) with 64 in HFSpres.
fold F in HFapp, HFpres, HFSpres.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 ((3, fpos) :: own)
  lyc S2 W mem2 md2 k HJ2) as Hpres2.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
assert (HF8u : F < 8 * (F / 8) + 8)
  by (pose proof (Z.mod_pos_bound F 8 ltac:(lia)); pose proof (Z_div_mod_eq_full F 8); lia).
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8al : (SRH_SB + F / 8) mod 8 = 0).
{ unfold SRH_SB. destruct (srh_div8_of_mul64 F HFa64) as [E8 _]. rewrite E8.
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
set (SH := SRH_SB + F / 8) in *.
assert (HSHv : SH = 0x7fff8000 + F / 8) by reflexivity.
assert (HSHe : shadow_addr F = SH) by (rewrite HSHv; reflexivity).
(* ---- the state after the call: the twelve saves only; their bytes are above the call's window ---- *)
jafter_call_keep_pi HS 40%nat regs1 (mrestrict (w_H W) mem2) HP1 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview pa_segs). pose proof HKEPT as (K1 & _). apply K1; [lia | rewrite Rsp; lia].
  - lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs1) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env pa_val A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
clear HE1.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F).
{ rewrite <- R10. unfold w64 in Ha01. rewrite <- Ha01. f_equal; apply bv_eq; reflexivity. }
clear R10.
assert (E1_2 : ew Ev1 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD1 by lia; exact E2').
assert (E1_32 : ew Ev1 32 = Z_to_bv 64 SRH_SB) by (rewrite OLD1 by lia; exact E32).
(* atom 60 = the realigned sp (s1 and sp), 62 = SH *)
srh_prreg_raw HS (2%bv : bv 5) Rsp2. srh_prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (srh_denot_and_m32 Ev1 2 (spZ regs) (-128) E1_2 ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in Rsp2.
rewrite (srh_denot_and_m32_add0 Ev1 2 (spZ regs) (-128) E1_2 ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in Rs12.
pose proof (srh_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 sp1]) as E2v eqn:HE2 in HS.
assert (OLD2 : forall nn, (nn < 60)%nat -> ew E2v nn = ew Ev1 nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E2v 60 = Z_to_bv 64 sp1)
  by (rewrite HE2; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env pa_val A_LIM E2v) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
clear HE2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (srh_pi_set_reg Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned;
          symmetry; exact Rsp2)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (srh_pi_set_reg Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned;
          symmetry; exact Rs12)) as HS3 end.
clear HS; rename HS3 into HS.
pose proof (srh_pi_havoc_hi 62 E2v _ _ [Z_to_bv 64 SH] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E2v 62 [Z_to_bv 64 SH]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 62)%nat -> ew E3v nn = ew E2v nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E62 : ew E3v 62 = Z_to_bv 64 SH)
  by (rewrite HE3; exact (ew_havoc_new E2v 62 [Z_to_bv 64 SH] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI3 : img_env pa_val A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
clear HE3.
assert (E3_2 : ew E3v 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD3, OLD2 by lia; exact E1_2).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 SRH_SB) by (rewrite OLD3, OLD2 by lia; exact E1_32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 F) by (rewrite OLD3, OLD2 by lia; exact E44).
assert (E3_60 : ew E3v 60 = Z_to_bv 64 sp1) by (rewrite OLD3 by lia; exact E60).
assert (E3REG : forall r : nat, (r < 32)%nat -> ew E3v r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. rewrite OLD3, OLD2, OLD1 by lia. exact (EREG r Hr). }
assert (U60 : bv_unsigned (ew E3v 60) = sp1) by (rewrite E3_60; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = SH) by (rewrite E62; apply unsigned_lit_small; lia).
assert (U3_2 : bv_unsigned (ew E3v 2) = spZ regs) by (rewrite E3_2; apply unsigned_lit_small; lia).
(* the facts the engine needs of the three new base atoms, and the shadow alias of s2 *)
srh_add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U60; change (2 ^ 5) with 32; repeat split; lia).
srh_add_fact HS 44%nat (mkAF 4096 140737479966720 6)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U44; change (2 ^ 6) with 64; repeat split; lia).
srh_add_fact HS 62%nat (mkAF SRH_SB (SRH_SB + 2 ^ 44) 3)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U62; change (2 ^ 3) with 8;
        unfold SRH_SB; repeat split; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (srh_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 44 32 62 F SRH_SB E3_44 ltac:(lia) E3_32 E62))
    as HS3 end.
clear HS; rename HS3 into HS; srh_norm_pi HS.
(* the three regions the body writes: the machine frame's word at sp1 + 0x18, F's header, F's shadow *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ srh_W1 HS eq_refl
  ltac:(unfold region_ok, srh_W1; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply Hpres2; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, srh_W1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U60, ?U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ srh_F HS eq_refl
  ltac:(unfold region_ok, srh_F; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U44; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, srh_F; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U44, ?U60, ?U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ srh_SH HS eq_refl
  ltac:(unfold region_ok, srh_SH; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U62; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); rewrite <- HSHe;
        apply (proj1 (HFSpres o ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, srh_SH; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U62, ?U44, ?U60, ?U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; srh_norm_pi HS.
(* ---- run 2 (plain): +0x70 .. +0x1b0, to the MID cut ---- *)
srh_run_to_plain RUNTOP HS HJ2 SRM_CUT_MID.
{ (* the writes the journal admits: the machine frame's word, F's header, F's shadow *)
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?g ?xo ?ou ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' g xo ou stk spx fp b0 bc lyx ownx) end.
  repeat apply awr_ok_x_cons; try apply awr_ok_x_nil;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?U60, ?U44, ?U62, ?U3_2 in Ha;
    first
    [ lia
    | left; split; [left; lia | lia]
    | left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 ((3, fpos) :: own)
        lyc S2 W mem2 md2 k 3 fpos a HJ2 ltac:(left; reflexivity));
      first [left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; change (fs_frame_bytes 3) with 512; lia
            | right; unfold in_zr; cbn [fst snd]; fold F; rewrite HSHe; change (fs_frame_bytes 3 / 8) with 64; lia] ]. }
(* ---- THE MID CUT ---- *)
intros ms3 mat3 HS3 HJ3 HF3 HFr3 HG3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
apply (HMID cx fpos lyc S2 W ms3 md3 HPREX (srm_gspan_of_pre SK B cx HPREX)).
(* the shape of the state the engine certifies *)
pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms3 HS3 eq_refl) as Hms3.
destruct (srh_ms_shape pa_segs ms3 _ _ _ Hms3) as (Hresv & Hsvc & Hrom & Hfrg & Hfcs & Hpc).
(* the twelve saved words, from the machine frame's region (its last region) *)
lazymatch type of HS3 with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  let o := eval vm_compute in (nth_error (ss_mem ssx) 3) in
  lazymatch o with Some ?r =>
    pose proof (srh_pi_region_nth Ev ssx msx 3 r HS3 ltac:(vm_compute; reflexivity)) as HRstk end end.
cbn [ms_mem restrict mkst] in HRstk.
assert (SAVE : forall (r : nat) od,
  In (YP09.mkChunk od (CVal 8 (SOff r 0)))
    [YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
     YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
     YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  (r < 32)%nat ->
  rdword (aview pa_segs (w_H W) (ms_mem ms3)) (spZ regs + od) = Some (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))).
{ intros r od Hin Hr.
  apply srh_rdword_of_val_mem; [| apply bv_unsigned_in_range].
  change 8%nat with (N.to_nat 8).
  eapply (field_of_region (segs := pa_segs) _ _ 2 (spZ regs) _ (-96) 0 0 0 od 8 (SOff r 0));
    [exact HRstk | exact U3_2 | exact Hin | | | cbn; lia].
  - cbn [sv_denot]. rewrite Z.add_0_r, (E3REG r Hr), Z_to_bv_bv_unsigned. reflexivity.
  - exact (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 (Z.of_nat r)))). }
(* what run 2 kept: every byte outside its three windows *)
assert (UN2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((SH <= a < SH + 52) \/ (F <= a < F + 24) \/ (sp1 + 24 <= a < sp1 + 32)) ->
  aview pa_segs (w_H W) (ms_mem ms3) a = aview pa_segs (w_H W) mem2 a).
{ apply (kept_of_frame (segs := pa_segs) _ _ (w_H W) mem2 (ms_mem ms3)
    (fun a => (SH <= a < SH + 52) \/ (F <= a < F + 24) \/ (sp1 + 24 <= a < sp1 + 32)) HFr3).
  intros bb wlo whi a Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr;
    rewrite ?U60, ?U44, ?U62, ?U3_2 in Hr; lia|]).
  destruct Hin. }
(* the kept clause: run 1, frame_alloc_3, run 2 *)
set (Eh := fun a : Z => (fun _ : Z => False) a \/ aside_rng lyc SRM_CID fpos a).
assert (Hceil' : alloc_ceiling <= spZ regs - REAC_SERVED_MARK_AK) by lia.
assert (Hshi : spZ regs <= 2 ^ 64) by lia.
assert (KA : akept pa_segs B lyc Sc W memc W (ms_mem msA) (spZ regs - REAC_SERVED_MARK_AK) (spZ regs) Eh).
{ apply (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W memc W (ms_mem msA)
    (spZ regs - REAC_SERVED_MARK_AK) (spZ regs) Eh Eh (fun a => spZ regs - 128 <= a < spZ regs) HAR Hceil' Hshi).
  - apply (akept_refl SK pa_segs B LAWS Hsegs). intros a Ha. apply Hpres0. lia.
  - intros a Ha Hn. exact (UN1 a Ha Hn).
  - intros a _ Hp. exact (apresent_grows (w_H W) memc (ms_mem msA) a HG Hp).
  - intros a Ha. exact Ha.
  - intros a Ha. right. lia. }
rewrite Rsp in HKEPT.
assert (KB : akept pa_segs B lyc Sc W (ms_mem msA) W mem2 (sp1 - ESTACK) sp1 Eh).
{ apply (akept_of_acall_kept SK pa_segs B LAWS Hsegs lyc Sc W (ms_mem msA) W mem2 (sp1 - ESTACK) sp1
    (fun _ => False) Eh HKEPT). intros a []. }
assert (KAB : akept pa_segs B lyc Sc W memc W mem2 (spZ regs - REAC_SERVED_MARK_AK) (spZ regs) Eh).
{ apply (akept_trans SK pa_segs B LAWS Hsegs lyc Sc W memc Sc W (ms_mem msA) W mem2
    (spZ regs - REAC_SERVED_MARK_AK) (spZ regs) (sp1 - ESTACK) sp1 Eh Eh Eh Hceil' Hshi KA KB);
  [lia | lia | intros b m Hb; exact Hb | intros f Hf; exact Hf | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
assert (KC : akept pa_segs B lyc Sc W memc W (ms_mem ms3) (spZ regs - REAC_SERVED_MARK_AK) (spZ regs) Eh).
{ apply (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W mem2 W (ms_mem ms3)
    (spZ regs - REAC_SERVED_MARK_AK) (spZ regs) Eh Eh
    (fun a => (SH <= a < SH + 52) \/ (F <= a < F + 24) \/ (sp1 + 24 <= a < sp1 + 32)) HAR Hceil' Hshi KAB).
  - intros a Ha Hn. exact (UN2 a Ha Hn).
  - intros a _ Hp. exact (apresent_grows (w_H W) mem2 (ms_mem ms3) a HG3 Hp).
  - intros a Ha. exact Ha.
  - intros a [Ha | [Ha | Ha]].
    + left. change ((fun _ : Z => False) a \/ aside_rng lyc SRM_CID fpos a). right.
      unfold aside_rng, SRM_CID. right. left. unfold in_zr. cbn [fst snd]. fold F. rewrite HSHe.
      change (fs_frame_bytes 3 / 8) with 64. lia.
    + left. change ((fun _ : Z => False) a \/ aside_rng lyc SRM_CID fpos a). right.
      unfold aside_rng, SRM_CID. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
      change (fs_frame_bytes 3) with 512. lia.
    + right. lia. }
(* the descriptors and the file system *)
assert (FD2 : m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
{ lazymatch type of Hsame2 with same_but_materialized ?mA _ =>
    rewrite (same_but_materialized_wvb mA md2 Hsame2);
    destruct (wvb_fds_fs (m_vm_lazy mA) (m_vm_materialized md2) mA) as [A1 A2]; rewrite A1, A2;
    first [apply wvb_fds_fs | split; reflexivity] end. }
assert (FD3 : m_fds md3 = m_fds mdc /\ m_fs md3 = m_fs mdc).
{ unfold md3. destruct (wvb_fds_fs (m_vm_lazy md2) mat3 md2) as [A1 A2]. rewrite A1, A2. exact FD2. }
(* the presence of F and of its shadow *)
assert (PF : forall a, F <= a < F + SRM_FB -> apresent (w_H W) (ms_mem ms3) a).
{ intros a Ha. apply (apresent_grows (w_H W) mem2 (ms_mem ms3) a HG3).
  apply (proj1 (HFpres a ltac:(unfold SRM_FB in Ha; lia))). }
assert (PSH : forall a, SH <= a < SH + SRM_SHN -> apresent (w_H W) (ms_mem ms3) a).
{ intros a Ha. apply (apresent_grows (w_H W) mem2 (ms_mem ms3) a HG3).
  replace a with (shadow_addr F + (a - SH)) by (rewrite HSHe; lia).
  apply (proj1 (HFSpres (a - SH) ltac:(unfold SRM_SHN in Ha; lia))). }
(* the flag-address word at F + 504, as frame_alloc_3 left it *)
assert (FLW : rdword (aview pa_segs (w_H W) (ms_mem ms3)) (F + SRM_FLAGPTR) = Some FL).
{ rewrite <- Hflagw. replace (F + 512 - 8) with (F + SRM_FLAGPTR) by (unfold SRM_FLAGPTR; lia).
  apply srh_rdword_ext. intros i Hi. apply UN2; unfold SRM_FLAGPTR in *; lia. }
(* the read-only image: akept's image clause, and the relro window inside the image *)
assert (ROD : arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) (ms_mem ms3))).
{ intros a Hro Ho He. rewrite <- (HROD a Hro Ho He).
  assert (Himg : in_img pa_segs a).
  { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (srh_relro_img a Hr)]. }
  pose proof KC as (_ & _ & K3 & _).
  apply (K3 a Himg Ho He). intros HEa.
  change ((fun _ : Z => False) a \/ aside_rng lyc SRM_CID fpos a) in HEa. destruct HEa as [[] | Hsd].
  destruct (aside_rng_low SK pa_segs B LAWS Hsegs lyc S2 W mem2 md2 SRM_CID fpos a HAR2 Hin2 Hsd) as [_ Hni].
  exact (Hni Himg). }
(* ---- the MID state ---- *)
unfold srm_gi_mid, srm_base. cbv zeta.
split; [rewrite Hpc; reflexivity|].
split; [srh_pi_reg HS3; apply bv_eq; vm_compute; reflexivity|].
split; [exact Hresv|]. split; [exact Hsvc|]. split; [exact Hrom|]. split; [exact Hfrg|]. split; [exact Hfcs|].
split; [exact HJ3|].
split; [exact Hfrs2|]. split; [exact Hnin2|].
split; [apply set_fs_of_exists; exact Hfs2|].
split; [rewrite Eab2; apply Permutation_refl|].
split; [exists S2, W, mem2, md2; split; [exact HAR2|]; split; [exact Hfrs2 | exact Eab2]|].
split; [srh_pi_reg HS3; rewrite E3_60; reflexivity|].
split; [srh_pi_reg HS3; rewrite E3_60; reflexivity|].
split; [srh_pi_reg HS3; rewrite E3_2; reflexivity|].
split; [srh_pi_reg HS3; rewrite E62; reflexivity|].
split; [srh_pi_reg HS3; rewrite E3_44; reflexivity|].
split; [srh_pi_reg HS3; rewrite E3_44; reflexivity|].
split; [srh_pi_reg HS3; rewrite E3_32; reflexivity|].
split; [srh_pi_reg HS3; rewrite (E3REG 11%nat ltac:(lia)); unfold srm_name, aarg, argZ, w64;
       rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [srh_pi_reg HS3; rewrite (E3REG 10%nat ltac:(lia)); unfold srm_mk, aarg, argZ, w64;
       rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [srh_pi_reg HS3; rewrite (E3REG 3%nat ltac:(lia)); f_equal; apply bv_eq; reflexivity|].
split; [srh_pi_reg HS3; rewrite (E3REG 4%nat ltac:(lia)); f_equal; apply bv_eq; reflexivity|].
split; [srh_pi_reg HS3; rewrite (E3REG 27%nat ltac:(lia)); f_equal; apply bv_eq; reflexivity|].
split.
{ unfold srm_sp. fold regs. replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
  rewrite (SAVE 1%nat (-8) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)).
  unfold raZ. repeat f_equal. all: apply bv_eq; reflexivity. }
split.
{ intros j Hj. unfold srm_sp. fold regs.
  assert (Hjs : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10) by lia.
  repeat (destruct Hjs as [Hjs | Hjs]; [subst j; srh_save_tac SAVE regs|]); subst j; srh_save_tac SAVE regs. }
split; [exact FLW|].
split; [exact PF|].
split; [exact PSH|].
split; [exact KC|].
split; [exact (proj1 FD3)|]. split; [exact (proj2 FD3)|].
split; [exact ROD|].
exact HFRM.
Qed.

End b.
End a.

About srm_head.
Print Assumptions srm_head.
