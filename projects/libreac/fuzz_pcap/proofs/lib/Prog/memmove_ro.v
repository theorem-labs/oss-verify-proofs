(* Frame v3 adapter of memmove (the roadapt tool form; ro_adapt with a u8arr transfer added by hand). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import memcpy_c memmove_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import memmove_ro_c memmove.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import RoAdapt.
Import ListNotations.
Open Scope bv_scope.

Lemma memmove_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u8arr_norm : forall m A bs, MemNorm.ro_agree rsegs m -> u8arr rsegs m A bs ->
  RoAdapt.not_ro rsegs A (Z.of_nat (length bs)) -> u8arr rsegs (MemNorm.normalize rsegs m) A bs.
Proof.
  intros m A bs HR [Hb Hw] Hn. split.
  - apply MemNorm.bytes_at_normalize; assumption.
  - apply RoAdapt.wr_at_norm'; assumption.
Qed.

Lemma u8arr_back : forall m m0 A bs, MemNorm.mem_rel rsegs m m0 -> u8arr rsegs m0 A bs -> u8arr rsegs m A bs.
Proof.
  intros m m0 A bs REL [Hb Hw]. split.
  - eapply RoAdapt.bytes_at_back; eassumption.
  - eapply MemNorm.wr_at_rel; eassumption.
Qed.

Ltac u8_pre segs HRO :=
  repeat match goal with
  | H : u8arr segs ?m ?A ?bs, Hn : RoAdapt.not_ro segs ?A _ |- _ =>
      lazymatch type of H with u8arr _ (MemNorm.normalize _ _) _ _ => fail | _ => idtac end;
      let H' := fresh "N" in pose proof (u8arr_norm m A bs HRO H Hn) as H'; clear H
  end.

Ltac ro_adapt_u8 segs WX :=
  let H := fresh "C" in intros H; red; intros;
  let HRO := match goal with h : MemNorm.ro_agree segs _ |- _ => h end in
  let m := match type of HRO with MemNorm.ro_agree _ ?m => m end in
  let REL := fresh "REL" in pose proof (MemNorm.mem_rel_normalize segs m HRO) as REL;
  u8_pre segs HRO; ro_pre segs HRO;
  pose proof (MemNorm.mem_inv_normalize segs m) as MIN;
  eapply evt_mono;
  [ eapply MemNorm.evt_normalize; [exact WX|exact HRO|]; eapply H; first [exact MIN | eassumption | assumption]
  | ];
  let s := fresh "s" in let s0 := fresh "s0" in let P := fresh "P" in let MR := fresh "MR" in let RS := fresh "RS" in
  intros s (s0 & P & MR & RS); red in P;
  repeat match type of P with exists _, _ => let x := fresh "x" in destruct P as [x P] end;
  repeat match type of P with _ /\ _ => let Q := fresh "Q" in destruct P as [Q P] end;
  match goal with Q : s0 = _ |- _ => subst s0 end;
  destruct s as [regs fregs pc svc resv fcsr mem rom];
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem);
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS;
  red;
  repeat match goal with |- exists _, _ => eexists end;
  repeat match goal with |- _ /\ _ => split end;
  [ unfold MS; subst; reflexivity | .. ];
  first [ ro_conj segs REL HRO | eapply u8arr_back; [eassumption|eassumption] ].

Theorem memmove_ro_of : memmove_contract -> memmove_ro_contract.
Proof. ro_adapt_u8 rsegs memmove_wx. Qed.

Theorem memmove_ro_holds : memcpy_contract -> memmove_ro_contract.
Proof. intros H1. exact (memmove_ro_of (memmove_holds H1)). Qed.
