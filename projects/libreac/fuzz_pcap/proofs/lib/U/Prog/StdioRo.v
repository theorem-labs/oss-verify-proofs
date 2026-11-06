From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Lemma stdio_ro_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mfile_cells_size : forall h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf,
  Z.of_nat (cells_size (mfile_cells h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf)) = 1304.
Proof. intros. reflexivity. Qed.

Lemma mfile_raw_norm : forall m h b n fl rpos rend md q prev next buf,
  MemNorm.ro_agree rsegs m -> mfile_raw m h b n fl rpos rend md q prev next buf -> RoAdapt.not_ro rsegs h 1304 ->
  mfile_raw (MemNorm.normalize rsegs m) h b n fl rpos rend md q prev next buf.
Proof.
  intros m h b n fl rpos rend md q prev next buf HR (pad0 & pad1 & pad2 & ung & C & R) HN.
  exists pad0, pad1, pad2, ung. split; [|exact R].
  apply RoAdapt.rw_cells_norm; [exact HR | exact C | rewrite mfile_cells_size; exact HN].
Qed.

Lemma mfile_norm : forall m h b Fc fl md q rb prev next,
  MemNorm.ro_agree rsegs m -> mfile m h b Fc fl md q rb prev next -> RoAdapt.not_ro rsegs h 1304 ->
  mfile (MemNorm.normalize rsegs m) h b Fc fl md q rb prev next.
Proof.
  intros m h b Fc fl md q rb prev next HR MF HN. unfold mfile in MF |- *. cbv zeta in MF |- *.
  destruct MF as (buf & RAW & R1 & R2 & BF & R3).
  exists buf. split; [exact (mfile_raw_norm _ _ _ _ _ _ _ _ _ _ _ _ HR RAW HN)|].
  split; [exact R1|]. split; [exact R2|]. split; [exact (MemNorm.bytes_at_normalize rsegs m b Fc HR BF) | exact R3].
Qed.

Lemma mstl_norm : forall m h b Fc p prev next,
  MemNorm.ro_agree rsegs m -> mstl m h b Fc p prev next -> RoAdapt.not_ro rsegs h 1304 ->
  mstl (MemNorm.normalize rsegs m) h b Fc p prev next.
Proof.
  intros m h b Fc p prev next HR (fl & md & q & rb & MF & R) HN.
  exists fl, md, q, rb. split; [exact (mfile_norm _ _ _ _ _ _ _ _ _ _ HR MF HN) | exact R].
Qed.

Lemma guard_ok_norm : forall m, MemNorm.ro_agree rsegs m -> guard_ok m -> guard_ok (MemNorm.normalize rsegs m).
Proof.
  intros m HR (G1 & g & G2). split; [exact (MemNorm.bytes_at_normalize rsegs m _ _ HR G1)|].
  exists g. exact (MemNorm.bytes_at_normalize rsegs m _ _ HR G2).
Qed.

Lemma mfile_raw_back : forall m m0 h b n fl rpos rend md q prev next buf, MemNorm.mem_rel rsegs m m0 ->
  mfile_raw m0 h b n fl rpos rend md q prev next buf -> mfile_raw m h b n fl rpos rend md q prev next buf.
Proof.
  intros m m0 h b n fl rpos rend md q prev next buf REL (pad0 & pad1 & pad2 & ung & C & R).
  exists pad0, pad1, pad2, ung. split; [exact (RoAdapt.rw_cells_back rsegs m m0 _ _ REL C) | exact R].
Qed.

Lemma mfile_back : forall m m0 h b Fc fl md q rb prev next, MemNorm.mem_rel rsegs m m0 ->
  mfile m0 h b Fc fl md q rb prev next -> mfile m h b Fc fl md q rb prev next.
Proof.
  intros m m0 h b Fc fl md q rb prev next REL MF. unfold mfile in MF |- *. cbv zeta in MF |- *.
  destruct MF as (buf & RAW & R1 & R2 & BF & R3).
  exists buf. split; [exact (mfile_raw_back _ _ _ _ _ _ _ _ _ _ _ _ _ REL RAW)|].
  split; [exact R1|]. split; [exact R2|]. split; [exact (RoAdapt.bytes_at_back rsegs m m0 _ _ REL BF) | exact R3].
Qed.

Lemma mstl_back : forall m m0 h b Fc p prev next, MemNorm.mem_rel rsegs m m0 ->
  mstl m0 h b Fc p prev next -> mstl m h b Fc p prev next.
Proof.
  intros m m0 h b Fc p prev next REL (fl & md & q & rb & MF & R).
  exists fl, md, q, rb. split; [exact (mfile_back _ _ _ _ _ _ _ _ _ _ _ REL MF) | exact R].
Qed.
