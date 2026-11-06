(* fs WRITER walk, image A (fs.asan): put's CLOSING THEOREM, `put_spec B tfibsegs` (lib/A/FSH_Fn_writer.v), by
   case on put's three arms (preset_file.c:454-476):
   - failed <> 0: lib/A/FSW_put_close.v put_close_failed (FSW_put.v put_failed_run);
   - failed = 0, the text fits: put_close_fast (FSW_put.v put_fast_run);
   - failed = 0, it does not: put_close_grow below = lib/A/FSW_put_grow_run.v fsw_pg_to_call (entry, both tests,
     the doubling loop, up to the fuzz_realloc call; FSW_put_grow_entry.v / FSW_put_grow.v) continued by
     lib/A/FSW_put_grow_tail.v pgt_run (the call, the resume at 0x84268, the granted and the refused tails).
   Section hypotheses (named, each with its owner): HSS (S0's shadow-base cells, FSH_Base.v FsShadowSyms; S0 is
   discharging it shared), RT_memcpy (the __asan_memcpy interceptor's contract, FSH_Rt.v's fr_memcpy field;
   RUNTIME), IMG (fs_img_facts, FSH_Rt.v; RELOC / RUNTIME), HREALLOC (fuzz_realloc_spec, FSH_Fn_alloc.v; ALLOC). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_writer_tbl FSW_put FSW_put_close FSW_put_grow FSW_put_grow_model FSW_put_grow_run
FSW_put_grow_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HREALLOC : fuzz_realloc_spec tfibsegs B.

(* the GROW arm in put_spec's form: the first half's continuation is exactly pgt_run's hand-over *)
Lemma put_close_grow :
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  zbytes_at tfibsegs W mem s bs -> wsrc_kept B tfibsegs ly S U W mem buf s bs -> Z.of_nat (length bs) = n ->
  WriterSpec.bytes_ok bs ->
  0 <= s /\ s + n <= alloc_ceiling -> (s + n <= o \/ ot <= s) ->
  Z.of_nat (length text) + n + 1 <= WMAX ->
  cap <= WMAX -> cap <= live ->
  wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) ->
  failed = 0 -> cap < Z.of_nat (length text) + n + 1 ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
    (put_post B ly S U W regs mem md ot o s n buf cap failed text bs live peak cnt fail).
Proof.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE FH G10 G11 G12 HOUT HGLOB HHEAD Hspo Hoot Hot16 Hottop HCHN HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM HCAP
  HCL HBUD HF0 HGROW.
subst failed.
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _ & _ & _ & _ & _ & _ & Hcase).
assert (Hcls : cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j)
  by (destruct Hcase as [(Hc0 & _) | (Hj & _)]; [left; exact Hc0 | right; exact Hj]).
assert (Hcap0 : 0 <= cap) by lia.
assert (Hc4096 : 4096 <= WriterSpec.newcap cap (Z.of_nat (length text) + n + 1))
  by exact (put_grow_newcap_ge_4096 cap _ Hcls).
assert (HcW : WriterSpec.newcap cap (Z.of_nat (length text) + n + 1) <= WMAX)
  by exact (put_grow_newcap_le cap _ Hcls HCAP HWM).
assert (Hcneed : Z.of_nat (length text) + n + 1 <= WriterSpec.newcap cap (Z.of_nat (length text) + n + 1))
  by exact (put_grow_need_le cap _ Hcls HWM).
apply (fsw_pg_to_call B HSS ly S U W regs mem md ch ot o n buf cap text _ HPRE G10 G12 HOUT Hspo Hoot Hot16 Hottop
         HPRESENT ltac:(lia) HWM HGROW).
intros E ms mdc HS _ HJ HARU HMF HPRK HEA HE36.
(* pgt_run's Section data by unification: every premise is a hypothesis here, and the candidate is newcap *)
eapply pgt_run; first [ eassumption | reflexivity ].
Qed.

(* ---- put's closing theorem ---- *)
Theorem put_holds : put_spec B tfibsegs.
Proof.
unfold put_spec.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE FH HFR G10 G11 G12 HOUT HGLOB HHEAD Hspo Hoot Hot16 Hottop HCHN HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM
  HCAP HCL HBUD.
destruct (Z.eq_dec failed 0) as [HF0 | HF1].
- destruct (Z_le_gt_dec (Z.of_nat (length text) + n + 1) cap) as [HFAST | HGROW].
  + exact (put_close_fast B HSS RT_memcpy IMG ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
             HPRE FH G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM HCAP
             HBUD HF0 HFAST).
  + exact (put_close_grow ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
             HPRE FH G10 G11 G12 HOUT HGLOB HHEAD Hspo Hoot Hot16 Hottop HCHN HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj
             HWM HCAP HCL HBUD HF0 ltac:(lia)).
- exact (put_close_failed B HSS ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
           HPRE G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HSRC HCAP HF1).
Qed.

End w.
