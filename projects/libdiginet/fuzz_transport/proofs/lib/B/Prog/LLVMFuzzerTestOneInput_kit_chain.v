(* LLVMFuzzerTestOneInput_kit_chain: kit statement K7 of the image-B walk of LLVMFuzzerTestOneInput
   (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v lc_chain_stmt; the image-A twin lib/A/Prog/LLVMFuzzerTestOneInput_kit_chain.v): at any loop cut, the frame-pointer chain the callees see
   from sp1 (the realigned sp) and s0 = sp0 (the entry sp).
   proves no function (kind: kit lemma of LLVMFuzzerTestOneInput's walk).
   - If sp0 lies within 16 bytes of ly_top, YCbq.v achain's first case gives the chain [].
   - Otherwise the chain is the one record [sp0, RA_LLVMF, the driver's s0]: lc_saved (lc_core) gives the saved ra and s0
     at sp0 - 8 and sp0 - 16 (LF_SAVED's (8, 1) and (16, 8)), the slot's pre gives raZ = RA_LLVMF >= 4096 and sp0
     16-aligned, and lc_core's sp1 <= sp0 - LF_FRAME gives sp1 + 16 <= sp0. When the driver's s0 is not a further
     record (bad_next), the chain ends there. Otherwise the slot's pre states the entry chain [] at sp0 and that s0
     (afn_pre ... []), whose only possible case is fpchain's [] (the s0 above sp0 >= alloc_ceiling): a word below 4096
     at s0 - 8. That word is kept to the cut: the G journal keeps every byte from alloc_ceiling up outside
     [sp0 - LLVMF_STK, sp0), up to G, and G_HARNESS_B lies below alloc_ceiling (lib/B/Prog/DgnTransportBCg.v inG_G_HARNESS_hull).
   So the spine is [] or [RA_LLVMF]. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Open Scope Z_scope.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.

Section chain. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

Lemma lc_chain_ok : @lc_chain_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_chain_stmt.
intros _ cx ly' S' W' regs' mem' md' e HB HC.
unfold lc_base, tfib_lib_pre_x in HB.
destruct HB as (HAFN & Hra & _).
destruct HAFN as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch0 & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & Htopsp & Htophi).
destruct HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & HSAV & _).
unfold lc_saved, LF_SAVED in HSAV.
inversion HSAV as [|o1 l1 Hra' HSAV1]; subst. inversion HSAV1 as [|o2 l2 Hs0' _]; subst.
cbn [fst snd] in Hra', Hs0'.
assert (Era : bv_unsigned (YK11.getr (l_regs cx) (Z_to_bv 5 1)) = RA_LLVMF) by exact Hra.
assert (Ecs : bv_unsigned (YK11.getr (l_regs cx) (Z_to_bv 5 8)) = s0Z (l_regs cx)) by reflexivity.
rewrite Era in Hra'. rewrite Ecs in Hs0'.
assert (Ra4 : 4096 <= RA_LLVMF) by (unfold RA_LLVMF; lia).
(* the pre states its facts at its own spZ / s0Z; restate them at lc_sp0 and s0Z (the same words) *)
assert (Hsp0al' : lc_sp0 cx mod 16 = 0) by exact Hsp0al.
assert (Hslo' : ly_stk_lo (l_ly cx) + LLVMF_STK <= lc_sp0 cx) by exact Hslo.
assert (Htopsp' : lc_sp0 cx <= ly_top (l_ly cx)) by exact Htopsp.
assert (Hch0' : ((s0Z (l_regs cx) < alloc_ceiling \/ ly_top (l_ly cx) - 16 <= s0Z (l_regs cx) \/
                  s0Z (l_regs cx) mod 8 <> 0) /\ (@nil (Z * Z * Z)) = []) \/
                (lc_sp0 cx + 16 <= s0Z (l_regs cx) /\ s0Z (l_regs cx) < ly_top (l_ly cx) - 16 /\
                 s0Z (l_regs cx) mod 8 = 0 /\
                 fpchain (rdword (aview segs (w_H (l_W cx)) (l_mem cx))) (s0Z (l_regs cx)) (ly_top (l_ly cx)) [] /\
                 Forall (fun r : Z * Z * Z => lc_sp0 cx + 16 <= fst (fst r)) (@nil (Z * Z * Z))))
  by (unfold achain in Hch0; exact Hch0).
clear Hsp0al Hslo Htopsp Hch0.
rename Hsp0al' into Hsp0al, Hslo' into Hslo, Htopsp' into Htopsp, Hch0' into Hch0.
destruct HJ as (_ & _ & (memS & HJd & Hag) & _).
destruct HJd as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Htop & _).
unfold lc_sp1 in *.
set (sp0 := lc_sp0 cx) in *.
set (cs0 := s0Z (l_regs cx)) in *.
set (rd' := aview segs (w_H W') mem').
set (rd0 := aview segs (w_H (l_W cx)) (l_mem cx)).
(* alloc_ceiling is the run's ceiling (YM05.v RunCeil), at least 0x7fff7f800000 (YCbq.v asan_consts) *)
pose proof YCbq.asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
(* every byte at or above sp0 is the entry's *)
assert (KEEP : forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd0 a).
{ intros a Ha. unfold rd', rd0.
  rewrite (F1 a ltac:(lia) ltac:(lia)).
  apply (aview_gagree segs TG.G_HARNESS_B _ _ _ a Hag).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a).
  { apply YP03.unsigned_lit_small. lia. }
  rewrite Ua. apply inGb_false. intros HG.
  pose proof (inG_G_HARNESS_hull a HG) as Hh. unfold TG.G_HARNESS_B_HI in Hh. lia. }
assert (Hal8 : sp0 mod 8 = 0) by (clear - Hsp0al; Z.div_mod_to_equations; lia).
assert (Hs1 : 32 * ((sp0 - LF_FRAME) / 32) + 16 <= sp0) by (clear - Hsp1; unfold LF_FRAME in *; lia).
unfold achain.
destruct (Z_le_gt_dec (ly_top (l_ly cx) - 16) sp0) as [Hhi | Hlo].
- (* sp0 within 16 bytes of ly_top: the chain [] *)
  exists []. split; [|left; reflexivity].
  left. split; [right; left; rewrite Htop; exact Hhi | reflexivity].
- exists [(sp0, RA_LLVMF, cs0)]. split; [|right; reflexivity].
  right. rewrite Htop.
  split; [exact Hs1|]. split; [lia|]. split; [exact Hal8|].
  split; [|constructor; [cbn [fst]; exact Hs1 | constructor]].
  cbn [fpchain].
  split; [reflexivity|]. split; [exact Hal8|]. split; [exact Hra'|]. split; [exact Hs0'|]. split; [exact Ra4|].
  destruct (bad_next sp0 (ly_top (l_ly cx)) cs0) eqn:Hbad; [reflexivity|].
  unfold bad_next in Hbad. apply Bool.orb_false_elim in Hbad as [Hbad Hm]. apply Bool.orb_false_elim in Hbad as [Hb1 Hb2].
  apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
  (* the entry chain [] at sp0 and cs0 is fpchain's []: a word below 4096 at cs0 - 8 *)
  destruct Hch0 as [(Hbadc & _) | (Hc16 & Hctop & _ & Hfp & _)].
  + exfalso. destruct Hbadc as [Hc | [Hc | Hc]].
    * lia.
    * lia.
    * apply Hc. apply negb_false_iff in Hm. apply Z.eqb_eq in Hm. exact Hm.
  + cbn [fpchain] in Hfp. destruct Hfp as (r & Hr & Hr4).
    exists r. split; [|exact Hr4].
    rewrite (YCbq.rdword_ext rd0 rd' (cs0 - 8)); [exact Hr|].
    intros k Hk. apply KEEP. lia.
Qed.

End chain.
