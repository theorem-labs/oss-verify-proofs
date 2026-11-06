(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFfi.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/AFfi.v, with its module paths and module names changed; 392 of its 466 lines of code are new or changed and 398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S4.v, with its addresses and numbers changed; 284 of its 404 lines of code are new or changed and 346 lines of the source are left out. *)
(* fuzz_state image A: the thin realloc segment S3 (RGtop.seg_ret): Deallocate's return into Reallocate ->
   realloc's return (a0 = the new block q), through Reallocate's, asan_realloc's and the interceptor's epilogues.

   Rule 24 (a Theorem Labs lane 02:59Z form, a Theorem Labs lane L12-RtResume.md): proves function __asan::Allocator::Reallocate chain (fs
   image A: __wrap_realloc 0x53078 -> __interceptor_realloc 0x53474 -> __asan::asan_realloc 0x3287c ->
   __asan::Allocator::Reallocate 0x32928), segment S3; reuse search (proof-index by name and by every address,
   2026-10-29 03:50-03:56Z, (internal path); cold branches, (internal path)) found no
   srealizes proof; the only hit is fs's bespoke line (template below).  The
   donor is cgif_rgb's released realloc family (lib/YF78.v:553, with YF6s-YF6u / YF67 / YF63 / YF68 / YF6o / YF6p);
   the machine run of this segment is ported from that family (YF78.v:437 succ_leaf's machine part), through
   a Theorem Labs lane's shared thin-segment statement (lib/Reusable/RGtop.v, seg_ret).  The machine run below is the fuzz_reply
   port of the same donor (plugin-hostd/fuzz_reply RT/RTm2.v:110 m3, RTk.v addresses) relocated to fuzz_state.asan
   (pinned sha256 64b53ff86172bb07...), with the fs addresses of FSRealloc_inst.v's header (S3 target).

   PORTED FILES (named per the owner's gate):
   - machine-run shape:  proofs/plugin-hostd/fuzz_reply/lib/RT/RTm2.v:110 (m3), RTm.v:38/47 (c8 / val_mem_addr),
     RTm2.v:34-44/50-108 (RFR / AFR / IFR regions, chunk8_atom / chunk8_lit / vm_vis / ret_post / ifr_chunks),
     both from cgif_rgb YF78.v:437 succ_leaf (frame/REALLOC-THIN-SEGMENTS.md m3).  Relocated: RT_RA_D ->
     FS_RA_DEALLOC 0x32a28, RT_RA_R -> FS_RA_REALLOCATE 0x32918, RT_RA_I -> FS_RA_ASAN_REALLOC 0x53620, rt_tbl ->
     s3_tbl (fs.asan addresses).
   - the segment statement and instance: lib/Reusable/RGtop.v (seg_ret), lib/A/FSRealloc_inst.v (K3_fs, FS_ARX,
     the FS_RA_* / frame literals), both read, not copied.

   The three pcs and their epilogues on A (capstone over the pinned fs.asan; RV64, no compressed instructions):
   - Reallocate's epilogue: 0x32a28 `mv a0, s4`, 0x32a2c `ld ra, 0x28(sp)`, 0x32a30-0x32a40 `ld s0..s4`,
     0x32a44 `addi sp, sp, 0x30`, 0x32a48 `ret` (-> ra = 0x32918);
   - asan_realloc: 0x32918 `beqz a0, -0x20` (a0 = q <> 0, NOT taken), 0x3291c `ld ra, 8(sp)`, 0x32920
     `addi sp, sp, 0x10`, 0x32924 `ret` (-> ra = 0x53620);
   - interceptor: 0x53620 `addi sp, sp, 0x70`, 0x53624-0x53640 `ld ra, s0..s6`, 0x53644 `addi sp, sp, 0x7f0`,
     0x53648 `ret` (-> the saved entry ra = realloc's return).
   TEMPLATE ONLY (owner's final ruling a Theorem Labs lane 04:50Z: bespoke `realizes`/rz_cut proofs are never bridged):
   fs's pre-ruling bespoke ricptD, a working branch lib/AZ/AsanW/
   F_arealloc_iseg.v:127-131 (ricptD_spec, the same start 0x32a28 at sp - 2208 and the same three epilogues to the
   caller); this file walks RGtop's seg_ret on the S0 `SRr` / `srealizes` kit instead.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSRealloc_inst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

Section fs_s3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The decode table of the three epilogue runs.                                                                      *)
Definition s3_tbl_build : ctable :=
build_table tfibsegs 0x32918 4%nat
(build_table tfibsegs 0x32a28 9%nat
(build_table tfibsegs 0x53620 11%nat TEmpty)).
Definition s3_tbl : ctable := Eval vm_compute in s3_tbl_build.
Lemma s3_tbl_eq : s3_tbl = s3_tbl_build.
Proof. vm_cast_no_check (@eq_refl ctable s3_tbl). Qed.
Lemma s3_tbl_ok : table_ok tfibsegs s3_tbl.
Proof.
rewrite s3_tbl_eq. unfold s3_tbl_build.
do 2 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Byte-and-word lemmas (image-local).                                                                               *)
Definition c8 (o : Z) (e : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 e).
Lemma val_mem_addr : forall m a a' (n : nat) v, val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.

Lemma vis_apresent_hi : forall (H : word -> bool) (m : word -> option byte) a, AF0x.TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:E; [|exfalso; apply Hv; reflexivity].
exact (AF0x.mbyte_high_apresent H m a b Ha E).
Qed.

Lemma apres_view1 : forall (H : word -> bool) mem a, apresent H mem a -> exists b : byte, aview tfibsegs H mem a = Some (bv_unsigned b).
Proof. intros H mem a Hp. destruct (AF0x.apresent_mbyte H mem a Hp) as [b Hb]. exists b. unfold aview. rewrite Hb. reflexivity. Qed.

Lemma word_of_present : forall (H : word -> bool) mem a,
apresent H mem a -> apresent H mem (a + 1) -> apresent H mem (a + 2) -> apresent H mem (a + 3) ->
apresent H mem (a + 4) -> apresent H mem (a + 5) -> apresent H mem (a + 6) -> apresent H mem (a + 7) ->
exists v, 0 <= v < 2 ^ 64 /\ val_mem tfibsegs (mrestrict H mem) a 8 v.
Proof.
intros H mem a P0 P1 P2 P3 P4 P5 P6 P7.
destruct (apres_view1 _ _ _ P0) as (c0 & A0). destruct (apres_view1 _ _ _ P1) as (c1 & A1).
destruct (apres_view1 _ _ _ P2) as (c2 & A2). destruct (apres_view1 _ _ _ P3) as (c3 & A3).
destruct (apres_view1 _ _ _ P4) as (c4 & A4). destruct (apres_view1 _ _ _ P5) as (c5 & A5).
destruct (apres_view1 _ _ _ P6) as (c6 & A6). destruct (apres_view1 _ _ _ P7) as (c7 & A7).
pose proof (u8_range c0). pose proof (u8_range c1). pose proof (u8_range c2). pose proof (u8_range c3).
pose proof (u8_range c4). pose proof (u8_range c5). pose proof (u8_range c6). pose proof (u8_range c7).
exists (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
split; [lia|].
apply (YCbq.val_mem_of_rdword tfibsegs). unfold rdword.
rewrite A0, A1, A2, A3, A4, A5, A6, A7. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The frame regions below realloc's entry sp, based at atom 2 (the sp at the start of the run = spZ regsD).  Atoms
   32..36: Reallocate's saved s4..s0; 37: the saved entry ra (vra); 38..44: the interceptor's saved s0..s6.          *)
Definition RFR (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 wlo whi
[c8 0 (SOff 32 0); c8 8 (SOff 33 0); c8 16 (SOff 34 0); c8 24 (SOff 35 0); c8 32 (SOff 36 0);
 c8 40 (SLit FS_RA_REALLOCATE)].
Definition AFR (b : Z) : YP09.region := YP09.mkRegion (Some 2%nat) b (b + 16) 0 0 [c8 (b + 8) (SLit FS_RA_ASAN_REALLOC)].
Definition IFR (b : Z) : YP09.region := YP09.mkRegion (Some 2%nat) b (b + 64) 0 0
[c8 b (SOff 44 0); c8 (b + 8) (SOff 43 0); c8 (b + 16) (SOff 42 0); c8 (b + 24) (SOff 41 0); c8 (b + 32) (SOff 40 0);
 c8 (b + 40) (SOff 39 0); c8 (b + 48) (SOff 38 0); c8 (b + 56) (SOff 37 0)].
Definition S3st : sstate :=
mkSS FS_RA_DEALLOC sr_atoms [RFR 0 0; AFR 48; IFR 2144] None (mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 0)] [] []).

Definition xvals (w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z) : list word :=
[w64 w0; w64 w1; w64 w2; w64 w3; w64 w4; w64 vra; w64 vs0; w64 vs1; w64 vs2; w64 vs3; w64 vs4; w64 vs5; w64 vs6].

Lemma chunk8_atom : forall regs (extra : list word) m base off j v,
nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs (Ereg regs extra) m base (c8 off (SOff (32 + j) 0)).
Proof.
intros regs extra m base off j v Hn Hv Hm. apply (chunk_ok_val tfibsegs _ m base off 8 (SOff (32 + j) 0) v); [|cbn; lia|cbn; lia|exact Hm].
cbn [sv_denot]. rewrite ew_Ereg_extra, Hn. rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.
Lemma chunk8_lit : forall E m base off v, 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (base + off) 8 v ->
YP09.chunk_ok tfibsegs E m base (c8 off (SLit v)).
Proof. intros E m base off v Hv Hm. apply (chunk_ok_val tfibsegs E m base off 8 (SLit v) v); [reflexivity|cbn; lia|cbn; lia|exact Hm]. Qed.
Lemma vm_vis : forall (H : word -> bool) mem a (w : nat) v i, val_mem tfibsegs (mrestrict H mem) a w v -> 0 <= i < Z.of_nat w ->
aview tfibsegs H mem (a + i) <> None.
Proof.
intros H mem a w v i Hv Hi. unfold aview. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.

Section W.
Variable W : world tfibsegs.
Variable md : Model.
Local Notation H := (w_H W).

Definition rfr_ok (m : word -> option byte) (a w0 w1 w2 w3 w4 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) a 8 w0 /\ val_mem tfibsegs (mrestrict H m) (a + 8) 8 w1 /\
val_mem tfibsegs (mrestrict H m) (a + 16) 8 w2 /\ val_mem tfibsegs (mrestrict H m) (a + 24) 8 w3 /\
val_mem tfibsegs (mrestrict H m) (a + 32) 8 w4 /\ val_mem tfibsegs (mrestrict H m) (a + 40) 8 FS_RA_REALLOCATE.
Definition afr_ok (m : word -> option byte) (a : Z) : Prop := val_mem tfibsegs (mrestrict H m) (a + 8) 8 FS_RA_ASAN_REALLOC.
Definition ifr_ok (m : word -> option byte) (a vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z) : Prop :=
val_mem tfibsegs (mrestrict H m) (a + 56) 8 vra /\ val_mem tfibsegs (mrestrict H m) (a + 48) 8 vs0 /\
val_mem tfibsegs (mrestrict H m) (a + 40) 8 vs1 /\ val_mem tfibsegs (mrestrict H m) (a + 32) 8 vs2 /\
val_mem tfibsegs (mrestrict H m) (a + 24) 8 vs3 /\ val_mem tfibsegs (mrestrict H m) (a + 16) 8 vs4 /\
val_mem tfibsegs (mrestrict H m) (a + 8) 8 vs5 /\ val_mem tfibsegs (mrestrict H m) a 8 vs6.

(* realloc's return: the interceptor's callee-saved registers restored, a0 = [a0], memory [MR]. *)
Definition ret_post (regs : bvmap 5 word) (MR : (word -> option byte) -> Prop) (sp' a0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z)
(W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\ MR mem' /\
getr regs' 2 = w64 sp' /\ getr regs' 1 = w64 vra /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\
getr regs' 18 = w64 vs2 /\ getr regs' 19 = w64 vs3 /\ getr regs' 20 = w64 vs4 /\ getr regs' 21 = w64 vs5 /\
getr regs' 22 = w64 vs6 /\ getr regs' 10 = w64 a0 /\
(forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).

Ltac reg_ent HS r k :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_nat _ _ k r eq_refl).
Ltac reg_x HS r j :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_extra _ _ j).
Ltac range8 := match goal with RV : Forall _ _ |- _ =>
  repeat (apply Forall_cons_iff in RV as [? RV]) end.

Ltac ifr_chunks regs X m sp b vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7 :=
  apply Forall_cons; [apply (chunk8_atom regs X m sp b 12 vs6); [reflexivity|lia|eapply val_mem_addr; [exact I7|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 8) 11 vs5); [reflexivity|lia|eapply val_mem_addr; [exact I6|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 16) 10 vs4); [reflexivity|lia|eapply val_mem_addr; [exact I5|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 24) 9 vs3); [reflexivity|lia|eapply val_mem_addr; [exact I4|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 32) 8 vs2); [reflexivity|lia|eapply val_mem_addr; [exact I3|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 40) 7 vs1); [reflexivity|lia|eapply val_mem_addr; [exact I2|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 48) 6 vs0); [reflexivity|lia|eapply val_mem_addr; [exact I1|lia]]|];
  apply Forall_cons; [apply (chunk8_atom regs X m sp (b + 56) 5 vra); [reflexivity|lia|eapply val_mem_addr; [exact I0|lia]]|];
  apply Forall_nil.

Lemma s3_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (sp qa w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 : Z),
bv_unsigned (getr regs 2) = sp -> 0x5fb000 <= sp -> sp + 2208 <= 2 ^ 64 ->
getr regs 20 = w64 qa -> 4096 <= qa <= 2 ^ 47 ->
Forall (fun v => 0 <= v < 2 ^ 64) [w0; w1; w2; w3; w4; vra; vs0; vs1; vs2; vs3; vs4; vs5; vs6] ->
rfr_ok mem sp w0 w1 w2 w3 w4 -> afr_ok mem (sp + 48) -> ifr_ok mem (sp + 2144) vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 ->
YK0s.ret_ok (w64 vra) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 FS_RA_DEALLOC) mem (seg_rom tfibsegs)) md)
(ret_post regs (fun m' => forall x, m' x = mem x) (sp + 2208) qa vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
Proof.
intros regs mem sp qa w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 Hsp Hlo Hhi G20 Hq RV
(F0 & F1 & F2 & F3 & F4 & F5) A0 (I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7) Hret.
pose proof AF0x.Hwx_tfa as Hwx. range8.
set (X := xvals w0 w1 w2 w3 w4 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6).
assert (E2 : bv_unsigned (ew (Ereg regs X) 2) = sp) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E20 : ew (Ereg regs X) 20 = w64 qa) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact G20).
assert (HS : st_ok tfibsegs (Ereg regs X) S3st (restrict (w_H W) (mkst regs (w64 FS_RA_DEALLOC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S3st. change (w64 FS_RA_DEALLOC) with (Z_to_bv 64 FS_RA_DEALLOC). apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, RFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 0 0 w0); [reflexivity|lia|eapply val_mem_addr; [exact F0|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 8 1 w1); [reflexivity|lia|eapply val_mem_addr; [exact F1|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 16 2 w2); [reflexivity|lia|eapply val_mem_addr; [exact F2|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 24 3 w3); [reflexivity|lia|eapply val_mem_addr; [exact F3|lia]]|].
      apply Forall_cons; [apply (chunk8_atom regs X _ sp 32 4 w4); [reflexivity|lia|eapply val_mem_addr; [exact F4|lia]]|].
      apply Forall_cons; [apply chunk8_lit; [unfold FS_RA_REALLOCATE; lia|eapply val_mem_addr; [exact F5|lia]]|]. apply Forall_nil.
    + unfold region_ok, AFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply chunk8_lit; [unfold FS_RA_ASAN_REALLOC; lia|eapply val_mem_addr; [exact A0|lia]]|]. apply Forall_nil.
    + unfold region_ok, IFR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      ifr_chunks regs X (mrestrict (w_H W) mem) sp 2144 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 I0 I1 I2 I3 I4 I5 I6 I7.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, RFR, AFR, IFR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !E2. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E20. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [split; [lia | split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]]|]. exact I. }
change (w64 FS_RA_DEALLOC) with (Z_to_bv 64 FS_RA_DEALLOC) in HS |- *.
srr_run_sh s3_tbl_ok HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ : forall x, ms_mem msA x = mem x).
{ intros x. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [fst snd] in Hrg; lia|]). destruct Hin. }
clear HF HFr.
eapply (SRr_ret_at tfibsegs s3_tbl s3_tbl_ok Hwx W _); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
assert (R1 : getr (ms_regs msA) 1 = w64 vra) by reg_x HS (1%bv : bv 5) 5%nat.
exists (ms_regs msA), (ms_mem msA), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hret. rewrite Hret. reflexivity. }
split; [exact MEQ|].
split. { let R := fresh "R" in rreg HS (2%bv : bv 5) R; rewrite R, E2; reflexivity. }
split; [exact R1|].
split; [reg_x HS (8%bv : bv 5) 6%nat|]. split; [reg_x HS (9%bv : bv 5) 7%nat|]. split; [reg_x HS (18%bv : bv 5) 8%nat|].
split; [reg_x HS (19%bv : bv 5) 9%nat|]. split; [reg_x HS (20%bv : bv 5) 10%nat|]. split; [reg_x HS (21%bv : bv 5) 11%nat|].
split; [reg_x HS (22%bv : bv 5) 12%nat|].
split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; exact E20. }
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
  let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]).
destruct Hr.
Qed.
End W.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Image-local register / byte helpers (ported from plugin-hostd/fuzz_reply RT/RTs.v:47-83 ap_get / ap_mk /          *)
(* val_mem_xfer, which are themselves cgif_rgb YF6p.v register algebra); ap_list goes through YP01.In_bv_eq.        *)
Lemma val_mem_xfer : forall (Hh Hh' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs Hh' m' (a + Z.of_nat k) = aview tfibsegs Hh m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict Hh m) a n v -> val_mem tfibsegs (mrestrict Hh' m') a n v.
Proof.
intros Hh Hh' m m' a n v E V k Hk. specialize (V k Hk). specialize (E k Hk). unfold aview in E. rewrite V in E. cbn in E.
destruct (mbyte tfibsegs (mrestrict Hh' m') (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate]. cbn in E. injection E as E.
f_equal. apply bv_eq. exact E.
Qed.
Lemma apresent_vis_l : forall (Hh : word -> bool) (m : word -> option byte) a, apresent Hh m a -> aview tfibsegs Hh m a <> None.
Proof. intros Hh m a [Hh0 [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh0, Hb. discriminate. Qed.
Lemma w64_unsigned : forall w : word, w64 (bv_unsigned w) = w.
Proof. intros w. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
Lemma ap_get : forall (r1 r2 : bvmap 5 word) (k : Z) (r : bv 5),
aregs_preserved r1 r2 -> acallee_saved k -> bv_unsigned r = k -> getr r2 r = getr r1 r.
Proof. intros r1 r2 k r P Hk Hr. replace r with (Z_to_bv 5 k) by (subst k; apply Z_to_bv_bv_unsigned). apply P. exact Hk. Qed.
Lemma ap_mk : forall (r1 r2 : bvmap 5 word),
(forall k (r : bv 5), acallee_saved k -> bv_unsigned r = k -> getr r2 r = getr r1 r) -> aregs_preserved r1 r2.
Proof.
intros r1 r2 Hm k Hk. apply (Hm k); [exact Hk|]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 5) with 32. apply Z.mod_small. unfold acallee_saved in Hk. lia.
Qed.
(* aregs_preserved from the fifteen callee-saved registers named as bv literals. *)
Lemma ap_list : forall (r1 r2 : bvmap 5 word),
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr r1 r) ->
aregs_preserved r1 r2.
Proof.
intros r1 r2 H. apply ap_mk. intros k r Hk Hr. apply H. apply In_bv_eq. rewrite Hr.
unfold acallee_saved in Hk. vm_compute. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The segment proof.                                                                                                 *)
Section seg.
Variable B : asyms.
Variable Up : list (Z * Z).
Hypothesis HB : TfibSyms B.

Lemma same_io_wvb : forall (m : Model) mat, same_io m (with_vm_backing (m_vm_lazy m) mat m).
Proof. intros m mat. destruct m. repeat split; reflexivity. Qed.

Theorem fs_seg_ret : FS_seg_ret B Up.
Proof.
unfold FS_seg_ret, seg_ret.
intros ly S W regs mem md p n_old n ch q ly2 S2 W4 so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5
  ENT HK3 DPREh DPOSTh LP3.
unfold rentry, realloc_pre in ENT.
destruct ENT as ((ARX0 & Hra & Hsp16 & Hslo & Hbot & Hshi & HWINr & Hgp & Htp & HCH) & RP & HBLK & HFP & HA0 & HA1 & HN & HL & HU).
unfold K3_fs in HK3.
destruct HK3 as (HQ & INQ & LLE2 & K3ra & K3sp & K3s4 & K3kk & K3frame & K3win).
unfold dealloc_pre in DPREh.
destruct DPREh as (ARXd & RPd & _ret & _4k & _m16 & _slo & _bot & _shi & _pres & Dgp & Dtp
  & _a0 & _a1 & _a2 & _a3 & _a4 & _a5 & _sso & _so16 & _som & _sbp & _bp2 & _bpm & _len & _vso & _vso8 & _vbuf & _Intr & DP & _fpre).
unfold dealloc_post_raw in DPOSTh.
destruct DPOSTh as (ARX3 & LLE3 & WLE3 & PRS3 & SIO3 & FR3 & _ & PR3).
unfold ASTACK in *.
unfold FS_ARX in ARX0, ARXd, ARX3.
destruct ARXd as (_ & ARU2). destruct ARX3 as (_ & ARU3).
unfold fs_rframe in K3frame. unfold FS_RFRAME in *.
destruct K3frame as (VRa & VRb & VRc & VRd & VRe & VRf & VRg & VRh & VRi & VRj).
pose proof AF0x.Hwx_tfa as Hwx.
(* the stack windows of ly2 / ly3 are ly's *)
assert (Eslo2 : ly_stk_lo ly2 = ly_stk_lo ly) by (destruct LLE2 as (_&_&_&_&_&_&_&_&_&E&_); exact E).
assert (Eshi2 : ly_stk_hi ly2 = ly_stk_hi ly) by (destruct LLE2 as (_&_&_&_&_&_&_&_&_&_&E&_); exact E).
assert (Eslo3 : ly_stk_lo ly3 = ly_stk_lo ly2) by (destruct LLE3 as (_&_&_&_&_&_&_&_&_&E&_); exact E).
assert (Eshi3 : ly_stk_hi ly3 = ly_stk_hi ly2) by (destruct LLE3 as (_&_&_&_&_&_&_&_&_&_&E&_); exact E).
(* qa (= sptr_addr B ly2 q) bound: q is a live block of S2 *)
assert (RSn : 1 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (IN2 : In (sptr_addr B ly2 q, n) (ablocks B ly2 S2))
  by (unfold ablocks; apply in_map_iff; exists (q, n); split; [reflexivity | exact INQ]).
pose proof (al_blocks _ _ (AR_laws_ok tfibsegs B) ly2 S2 W4 (FSP.unpoison Up memD) mdD (sptr_addr B ly2 q) n
  (FSP.ARU_AR _ _ _ _ _ _ _ _ ARU2) IN2) as (_ & Q4096 & QC & _ & _ & _ & QN).
pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR. destruct HCR as ((_ & CH) & _).
assert (QHI : sptr_addr B ly2 q <= 2 ^ 47) by lia.
(* realloc's entry sp is high in the stack; ly_stk_lo ly >= kHighMemBeg, ly_stk_hi ly <= kHighMemEnd *)
pose proof (FSP.ARU_ARm tfibsegs B ly S Up W mem md (proj2 ARX0)) as ARm0.
pose proof (lo_top ly (am_layout B ly S _ ARm0)) as LT.
destruct LT as (_ & _ & _ & SHIle & _ & _ & SLOhi).
unfold kHighMemBeg in SLOhi. unfold kHighMemEnd in SHIle.
assert (SPlo : 0x5fb000 <= spZ regs - 2208) by lia.
assert (SPhi : spZ regs - 2208 + 2208 <= 2 ^ 64) by lia.
pose proof (ts_errno B HB) as HERR. unfold TFIB_ERRNO in HERR.
(* the old block of p is off the stack (for ~ E) *)
assert (PNOTSTK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
  ~ (p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old)).
{ intros a Ha [Hpn Hin]. destruct DP as [EP|INp]; [exact (Hpn EP)|].
  assert (INp2 : In (sptr_addr B ly2 p, n_old) (ablocks B ly2 S2))
    by (unfold ablocks; apply in_map_iff; exists (p, n_old); split; [reflexivity | exact INp]).
  exact (FSP.ARU_stack_not_block _ _ (AR_laws_ok tfibsegs B) ly2 S2 Up W4 memD mdD a ARU2
    ltac:(rewrite Eslo2, Eshi2; exact Ha) (sptr_addr B ly2 p) n_old INp2 Hin). }
(* ~ aowned at ly2 S2 and ly3 S3 for stack addresses *)
assert (OWN2 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly2 S2 a).
{ intros a Ha. apply (FSP.ARU_stack _ _ (AR_laws_ok tfibsegs B) ly2 S2 Up W4 memD mdD a ARU2).
  rewrite Eslo2, Eshi2; exact Ha. }
assert (OWN3 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly3 S3 a).
{ intros a Ha. apply (FSP.ARU_stack _ _ (AR_laws_ok tfibsegs B) ly3 S3 Up W5 mem5 md5 a ARU3).
  rewrite Eslo3, Eslo2, Eshi3, Eshi2; exact Ha. }
(* DPOST's frame transfer, for an address in realloc's window, outside Deallocate's stack scratch *)
assert (FRMV : forall a, spZ regs - 16384 <= a < spZ regs -> ~ (spZ regsD - DFSTACK_G <= a < spZ regsD) ->
  aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W4) memD a).
{ intros a Ha Hout. apply FR3.
  - lia.
  - apply OWN2; lia.
  - apply OWN3; lia.
  - unfold ascratch. rewrite HERR. intros [X|X]; [exact (Hout X) | lia].
  - apply PNOTSTK; lia. }
assert (FRXF : forall a (k : nat) v, spZ regs - 16384 <= a -> a + Z.of_nat k <= spZ regs -> spZ regs - 2208 <= a ->
  val_mem tfibsegs (mrestrict (w_H W4) memD) a k v -> val_mem tfibsegs (mrestrict (w_H W5) mem5) a k v).
{ intros a k v H1 H2 H3 V. apply (val_mem_xfer (w_H W4) (w_H W5) memD mem5 a k v); [|exact V].
  intros i Hi. apply FRMV; [lia | intros [Y1 Y2]; lia]. }
(* realloc's window is present at (W5, mem5) *)
assert (RWIN5 : forall a, spZ regs - 16384 <= a < spZ regs -> apresent (w_H W5) mem5 a).
{ intros a Ha.
  destruct (Z_lt_le_dec a (spZ regsD - DFSTACK_G)) as [C1|C1];
  [|destruct (Z_lt_le_dec a (spZ regsD)) as [C2|C2]].
  - apply vis_apresent_hi; [unfold AF0x.TFIB_IMG_END; lia|].
    rewrite (FRMV a Ha ltac:(intros [Y1 Y2]; lia)).
    exact (apresent_vis_l (w_H W4) memD a (K3win a Ha)).
  - apply PR3. lia.
  - apply vis_apresent_hi; [unfold AF0x.TFIB_IMG_END; lia|].
    rewrite (FRMV a Ha ltac:(intros [Y1 Y2]; lia)).
    exact (apresent_vis_l (w_H W4) memD a (K3win a Ha)). }
(* Reallocate's saved s0..s4 are present; read them off as the words w0..w4 *)
assert (GETW : forall a, spZ regs - 16384 <= a -> a + 8 <= spZ regs ->
  exists v, 0 <= v < 2 ^ 64 /\ val_mem tfibsegs (mrestrict (w_H W5) mem5) a 8 v).
{ intros a L1 L2. apply (word_of_present (w_H W5) mem5 a); apply RWIN5; lia. }
destruct (GETW (spZ regs - 2208) ltac:(lia) ltac:(lia)) as (w0 & W0r & W0m).
destruct (GETW (spZ regs - 2208 + 8) ltac:(lia) ltac:(lia)) as (w1 & W1r & W1m).
destruct (GETW (spZ regs - 2208 + 16) ltac:(lia) ltac:(lia)) as (w2 & W2r & W2m).
destruct (GETW (spZ regs - 2208 + 24) ltac:(lia) ltac:(lia)) as (w3 & W3r & W3m).
destruct (GETW (spZ regs - 2208 + 32) ltac:(lia) ltac:(lia)) as (w4 & W4r & W4m).
(* the s3_run hypotheses *)
assert (SP5 : bv_unsigned (getr regs5 2) = spZ regs - 2208).
{ rewrite (ap_get regsD regs5 2 2%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl). exact K3sp. }
assert (QA20 : getr regs5 20 = w64 (sptr_addr B ly2 q)).
{ rewrite (ap_get regsD regs5 20 20%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl). exact K3s4. }
assert (FORALLv : Forall (fun v => 0 <= v < 2 ^ 64) [w0; w1; w2; w3; w4; raZ regs;
  bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18); bv_unsigned (getr regs 19);
  bv_unsigned (getr regs 20); bv_unsigned (getr regs 21); bv_unsigned (getr regs 22)]).
{ apply Forall_cons; [exact W0r|]. apply Forall_cons; [exact W1r|]. apply Forall_cons; [exact W2r|].
  apply Forall_cons; [exact W3r|]. apply Forall_cons; [exact W4r|].
  apply Forall_cons; [unfold raZ; apply u64_range|].
  apply Forall_cons; [apply u64_range|]. apply Forall_cons; [apply u64_range|]. apply Forall_cons; [apply u64_range|].
  apply Forall_cons; [apply u64_range|]. apply Forall_cons; [apply u64_range|]. apply Forall_cons; [apply u64_range|].
  apply Forall_cons; [apply u64_range|]. apply Forall_nil. }
assert (RETok : YK0s.ret_ok (w64 (raZ regs)))
  by (replace (w64 (raZ regs)) with (getr regs 1) by (unfold raZ; rewrite w64_unsigned; reflexivity); exact Hra).
assert (RFRok : rfr_ok W5 mem5 (spZ regs - 2208) w0 w1 w2 w3 w4).
{ unfold rfr_ok.
  split; [exact W0m|]. split; [exact W1m|]. split; [exact W2m|]. split; [exact W3m|]. split; [exact W4m|].
  eapply val_mem_addr; [apply (FRXF (spZ regs - 2208 + 40) 8%nat FS_RA_REALLOCATE); [lia|lia|lia|exact VRa]|lia]. }
assert (AFRok : afr_ok W5 mem5 (spZ regs - 2208 + 48)).
{ unfold afr_ok.
  eapply val_mem_addr; [apply (FRXF (spZ regs - 2208 + 56) 8%nat FS_RA_ASAN_REALLOC); [lia|lia|lia|exact VRb]|lia]. }
assert (IFRok : ifr_ok W5 mem5 (spZ regs - 2208 + 2144) (raZ regs) (bv_unsigned (getr regs 8))
  (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
  (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22))).
{ unfold ifr_ok.
  split; [eapply val_mem_addr; [apply (FRXF (spZ regs - 8) 8%nat (raZ regs)); [lia|lia|lia|exact VRc]|lia]|].
  split; [eapply val_mem_addr; [apply (FRXF (spZ regs - 16) 8%nat (bv_unsigned (getr regs 8))); [lia|lia|lia|exact VRd]|lia]|].
  split; [eapply val_mem_addr; [apply (FRXF (spZ regs - 24) 8%nat (bv_unsigned (getr regs 9))); [lia|lia|lia|exact VRe]|lia]|].
  split; [eapply val_mem_addr; [apply (FRXF (spZ regs - 32) 8%nat (bv_unsigned (getr regs 18))); [lia|lia|lia|exact VRf]|lia]|].
  split; [eapply val_mem_addr; [apply (FRXF (spZ regs - 40) 8%nat (bv_unsigned (getr regs 19))); [lia|lia|lia|exact VRg]|lia]|].
  split; [eapply val_mem_addr; [apply (FRXF (spZ regs - 48) 8%nat (bv_unsigned (getr regs 20))); [lia|lia|lia|exact VRh]|lia]|].
  split; [eapply val_mem_addr; [apply (FRXF (spZ regs - 56) 8%nat (bv_unsigned (getr regs 21))); [lia|lia|lia|exact VRi]|lia]|].
  eapply val_mem_addr; [apply (FRXF (spZ regs - 64) 8%nat (bv_unsigned (getr regs 22))); [lia|lia|lia|exact VRj]|lia]. }
(* gp, tp and s7..s11 at Deallocate's return are realloc's entry values (Deallocate keeps them; K3_fs / DPRE) *)
assert (KK : forall (k : Z) (r : bv 5), 23 <= k <= 27 -> bv_unsigned r = k -> getr regsD r = getr regs r).
{ intros k r Hk Hr. replace r with (Z_to_bv 5 k) by (subst k; apply Z_to_bv_bv_unsigned). apply K3kk. exact Hk. }
assert (KEEP5 : forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs5 r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
  [ rewrite (ap_get regsD regs5 3 3%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl), Dgp, Hgp; reflexivity
  | rewrite (ap_get regsD regs5 4 4%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl), Dtp, Htp; reflexivity
  | rewrite (ap_get regsD regs5 23 23%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl); exact (KK 23 23%bv ltac:(lia) eq_refl)
  | rewrite (ap_get regsD regs5 24 24%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl); exact (KK 24 24%bv ltac:(lia) eq_refl)
  | rewrite (ap_get regsD regs5 25 25%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl); exact (KK 25 25%bv ltac:(lia) eq_refl)
  | rewrite (ap_get regsD regs5 26 26%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl); exact (KK 26 26%bv ltac:(lia) eq_refl)
  | rewrite (ap_get regsD regs5 27 27%bv PRS3 ltac:(unfold acallee_saved; lia) eq_refl); exact (KK 27 27%bv ltac:(lia) eq_refl) ]. }
(* run the machine, then rebuild seg_ret's post *)
change (cfg_at tfibsegs (raZ regsD) regs5 mem5 md5) with (mkCfg (mkst regs5 (w64 (raZ regsD)) mem5 (seg_rom tfibsegs)) md5).
rewrite K3ra.
eapply SRr_mono;
[ eapply (s3_run W5 md5 regs5 mem5 (spZ regs - 2208) (sptr_addr B ly2 q) w0 w1 w2 w3 w4 (raZ regs)
    (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
    (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22)));
  [ exact SP5 | exact SPlo | exact SPhi | exact QA20 | split; [exact Q4096 | exact QHI] | exact FORALLv
  | exact RFRok | exact AFRok | exact IFRok | exact RETok ]
| intros W' c' _ POST ].
destruct POST as (EW & regs' & mem' & mat & Ec & MEQ' & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P10 & PK).
subst W'.
exists regs', mem', (with_vm_backing (m_vm_lazy md5) mat md5).
split. { rewrite Ec. unfold cfg_at. reflexivity. }
split.
{ apply ap_list. intros r Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
  [ rewrite P2; unfold w64; replace (spZ regs - 2208 + 2208) with (bv_unsigned (getr regs 2)) by (unfold spZ; lia); apply Z_to_bv_bv_unsigned
  | rewrite PK by (cbn [In]; tauto); apply KEEP5; cbn [In]; tauto
  | rewrite PK by (cbn [In]; tauto); apply KEEP5; cbn [In]; tauto
  | rewrite P8; apply w64_unsigned
  | rewrite P9; apply w64_unsigned
  | rewrite P18; apply w64_unsigned
  | rewrite P19; apply w64_unsigned
  | rewrite P20; apply w64_unsigned
  | rewrite P21; apply w64_unsigned
  | rewrite P22; apply w64_unsigned
  | rewrite PK by (cbn [In]; tauto); apply KEEP5; cbn [In]; tauto
  | rewrite PK by (cbn [In]; tauto); apply KEEP5; cbn [In]; tauto
  | rewrite PK by (cbn [In]; tauto); apply KEEP5; cbn [In]; tauto
  | rewrite PK by (cbn [In]; tauto); apply KEEP5; cbn [In]; tauto
  | rewrite PK by (cbn [In]; tauto); apply KEEP5; cbn [In]; tauto ]. }
split; [exact P10|].
split.
{ unfold FS_ARX. split; [reflexivity|].
  apply (FSP.ARU_frame _ _ (AR_laws_ok tfibsegs B) ly3 S3 Up W5 mem5 md5 mem'
    (with_vm_backing (m_vm_lazy md5) mat md5) ARU3).
  - intros a _ _. apply AF0x.aview_same. apply MEQ'.
  - intros a Hv. rewrite (AF0x.aview_same (w_H W5) mem5 mem' a (MEQ' (Z_to_bv 64 a))). exact Hv.
  - apply m_vmmaps_wvb.
  - apply m_vm_lazy_wvb.
  - apply eager_used_wvb.
  - intros a _ _. apply MEQ'. }
split; [apply same_io_wvb|].
split.
{ split; [intros a _ _; apply AF0x.aview_same; apply MEQ' | intros x _; apply MEQ']. }
{ intros a Ha. apply (AF0x.apresent_same (w_H W5) mem5 mem' a (MEQ' (Z_to_bv 64 a))). apply RWIN5. unfold ASTACK in Ha; lia. }
Qed.
End seg.
End fs_s3.
