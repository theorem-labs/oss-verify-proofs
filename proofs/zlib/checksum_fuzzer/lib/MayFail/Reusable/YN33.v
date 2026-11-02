(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN33.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Section b.
Context {rc : YM05.RunCeil}.
Hypothesis AMH : forall fx : YK11.FPState, @alloc_meta_hyp fx rc src0_msyms.
Hypothesis MSH : forall fx : YK11.FPState, @malloc_small_hyp fx rc src0_msyms.
Hypothesis NTA : forall fx : YK11.FPState, @ntA_hyp fx rc src0_msyms.
Lemma src0_calloc_vacuous {fx : YK11.FPState} : calloc_realizes src0_msyms (MRx src0_msyms).
Proof. intros pc L A regs mem md m n Hpc. cbn in Hpc. discriminate Hpc. Qed.
Definition src0_API : AllocAPI src0_msyms :=
{| aa_MR := MRx src0_msyms;
aa_laws := MRx_laws src0_msyms;
aa_init := fun mem md sec H Hs => MRx_init src0_msyms mem md sec src0_syms_ok H Hs;
aa_malloc := fun fx => @src0_malloc_realizes fx rc (AMH fx) (MSH fx);
aa_free := fun fx => @src0_free_realizes fx rc (@src0_ntfree_of_A fx rc (NTA fx));
aa_free_null := fun fx => @src0_free_null fx;
aa_calloc := fun fx => @src0_calloc_vacuous fx |}.
End b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI04.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : malloc_syms.
Lemma MRc_owned_img_ctx : forall L A mem md a,
MRc B L A mem md -> in_img B a -> alloc_owned L A a -> ms_ctx B <= a < ms_ctx B + CTX_SIZE.
Proof.
intros L A mem md a M Himg [(rg & Hrg & Hx) _].
destruct (In_footprint_inv A rg Hrg) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- rewrite (mc_ctx _ _ _ _ _ M) in Hx. lia.
- exfalso. destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hx.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hr Hl) as (_ & _ & _ & Hoff).
apply (Hoff a); [unfold PGSZ in *; lia | exact Himg].
- exfalso. destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k r Hr Hl) as (_ & _ & _ & Hoff).
apply (Hoff a); [lia | exact Himg].
Qed.
Lemma MRc_blocks_img : forall L A mem md p n i,
MRc B L A mem md -> In (p, n) (user_blocks A) -> 0 <= i < n -> ~ in_img B (ptr_addr L p + i).
Proof.
intros L A mem md p n i M Hin Hi.
destruct (YN03.block_region A p n (mc_wf _ _ _ _ _ M) Hin) as (k & o & rg & -> & Hrg & Hkind & Hlive & Ho & Hn & Hlen & _).
unfold ptr_addr. cbn [loc_addr].
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rg Hrg Hlive) as (_ & _ & _ & Hoff).
apply Hoff. lia.
Qed.
Lemma MRc_statics : forall L A mem md,
MRc B L A mem md ->
word_mem (ms_segs B) mem (ms_got_guard B) (ms_guard B) /\
(exists g, 0 <= g < 2 ^ 64 /\ word_mem (ms_segs B) mem (ms_guard B) g) /\
mbyte (ms_segs B) mem (ms_libc B + 3) = Some (Z_to_bv 8 0).
Proof.
intros L A mem md M. pose proof (mc_statics _ _ _ _ _ M) as S.
split; [exact (st_got _ _ S)|]. split; [| exact (st_needlocks _ _ S)].
destruct (st_guard _ _ S) as [g Hg]. exists (g mod 2 ^ 64). split; [apply Z.mod_pos_bound; lia|].
intros k Hk. rewrite (Hg k Hk). f_equal. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
End d.
Section e.
Variable B : malloc_syms.
Theorem MRx_AllocExtra : AllocExtra B (MRx B).
Proof.
split.
- intros L A mem md a M. apply (MRc_owned_img_ctx B L A mem md a). apply MRx_MRc. exact M.
- intros L A mem md p n i M. apply (MRc_blocks_img B L A mem md p n i). apply MRx_MRc. exact M.
- intros L A mem md M. apply (MRc_statics B L A mem md). apply MRx_MRc. exact M.
Qed.
Theorem MRx_img_laws : syms_ok B -> img_laws B (MRx B).
Proof.
intros SO. split.
- intros a Ha. apply (so_img_hi _ SO a Ha).
- intros L A mem md p n i M. apply (MRc_blocks_img B L A mem md p n i). apply MRx_MRc. exact M.
- intros L A mem md a M. apply (MRc_owned_img_ctx B L A mem md a). apply MRx_MRc. exact M.
- intros L A mem md a M Ha. apply (st_tables _ _ (mc_statics _ _ _ _ _ (MRx_MRc _ _ _ _ _ M))). unfold table_addr. lia.
Qed.
End e.
End c.
