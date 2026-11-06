(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the entry predicate
   of the phase that starts where the fread of the 16-byte record header returns (NP_hd_ra, 0x81770), and the facts
   of Pau's model (lib/Prog/pcap_source_struct_next.v, PSN) that phase uses. The phase itself is
   lib/B/Prog/PcapSourceNextHdrB.v. The lib/A twin is lib/A/Prog/PcapSourceNextHdrBDefs.v (a Theorem Labs lane); this file
   states the same predicate over lib/B's phase layer (lib/B/Prog/PcapSourceNextDefs.v).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; capstone 5 disassembly of its unstripped twin). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The model                                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Section model.
Variables (sw : bool) (F : list byte) (cap : Z).

Lemma nx_fb_range : forall i, 0 <= PSN.fb F i < 256.
Proof.
  intros i. unfold PSN.fb.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) F (Z_to_bv 8 0))) as H.
  change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma nx_hw_range : forall q j, 0 <= PSN.hw sw F q j < 2 ^ 32.
Proof.
  intros q j. unfold PSN.hw, PSN.w32le.
  pose proof (nx_fb_range (q + j)) as H0. pose proof (nx_fb_range (q + j + 1)) as H1.
  pose proof (nx_fb_range (q + j + 2)) as H2. pose proof (nx_fb_range (q + j + 3)) as H3.
  destruct sw; lia.
Qed.

(* What each kind of record says about the file and the header (PSN.kind, one test per line). *)
Lemma nx_kind_cases : forall q,
  match PSN.kind sw F cap q with
  | PSN.KEnd => PSN.flen F - q = 0
  | PSN.KCutH => PSN.flen F - q <> 0 /\ PSN.flen F - q < 16
  | PSN.KEmpty => 16 <= PSN.flen F - q /\ PSN.incl sw F q = 0
  | PSN.KFit => 16 <= PSN.flen F - q /\ PSN.incl sw F q <> 0 /\ PSN.incl sw F q <= cap /\
                q + 16 + PSN.incl sw F q <= PSN.flen F
  | PSN.KCutFit => 16 <= PSN.flen F - q /\ PSN.incl sw F q <> 0 /\ PSN.incl sw F q <= cap /\
                   PSN.flen F < q + 16 + PSN.incl sw F q
  | PSN.KBig0 => 16 <= PSN.flen F - q /\ PSN.incl sw F q <> 0 /\ cap < PSN.incl sw F q /\ cap = 0
  | PSN.KBig => 16 <= PSN.flen F - q /\ PSN.incl sw F q <> 0 /\ cap < PSN.incl sw F q /\ cap <> 0 /\
                q + 16 + PSN.incl sw F q <= PSN.flen F
  | PSN.KCutBig => 16 <= PSN.flen F - q /\ PSN.incl sw F q <> 0 /\ cap < PSN.incl sw F q /\
                   cap <> 0 /\ PSN.flen F < q + 16 + PSN.incl sw F q
  end.
Proof.
  intros q. unfold PSN.kind.
  destruct (Z.eqb_spec (PSN.flen F - q) 0); [cbv beta iota; lia|].
  destruct (Z.ltb_spec (PSN.flen F - q) 16); [cbv beta iota; lia|].
  destruct (Z.eqb_spec (PSN.incl sw F q) 0); [cbv beta iota; lia|].
  destruct (Z.leb_spec (PSN.incl sw F q) cap).
  - destruct (Z.leb_spec (q + 16 + PSN.incl sw F q) (PSN.flen F)); cbv beta iota; lia.
  - destruct (Z.eqb_spec cap 0); [cbv beta iota; lia|].
    destruct (Z.leb_spec (q + 16 + PSN.incl sw F q) (PSN.flen F)); cbv beta iota; lia.
Qed.

End model.

(* ---------------------------------------------------------------------------------------------- *)
(* The entry predicate at NP_hd_ra (0x81770)                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* What the header fread (0x8176c) returns and writes: k = min 16 (|C| - q) bytes of the file from the turn's
   position q, into `ph` at F + 32 (NO_PH). *)
Definition nx_hk (C : list Z) (q : Z) : Z := Z.min NX_PH_LEN (Z.of_nat (length C) - q).
Definition nx_hdr (C : list Z) (q : Z) : list Z := firstn (Z.to_nat (nx_hk C q)) (skipn (Z.to_nat q) C).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* THE ENTRY PREDICATE AT NP_hd_ra (0x81770), where the fread of the 16-byte record header returns. The turn of the
   record loop started at the file position q with lh the last non-empty record header seen (nx_loop_inv's
   clauses); the fread has read k = nx_hk C q bytes: a0 = k, `ph` (F + 32) holds them, and the stream stands at
   q + k. The frame's shadow is NSH_ph (`ph` in scope since 0x8174c). Besides nx_mid's registers (s5 = ps, s7 = cap,
   s10 = shadow of ps, s11 = ps + 8) the phase reads s3 = ph = F + 32 (the rd_u32 argument at 0x81784 and the UBSan
   guards 0x81794 / 0x817b4 / 0x817d8) and s4 = the shadow address of ps + 8 (the shadow checks 0x81778, 0x81798,
   0x817b8, 0x817dc); both are callee-saved, so the fread kept them. R is the top's measure of the record loop
   (nx_loop_at): every q' after this turn's start is one the loop may go back to. *)
Definition nx_hdra_inv (R : ncx -> Z -> Prop) (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (q : Z) (lh : option Z),
  nx_next_ok R cx q /\
  nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 /\
  (* what the header fread did *)
  getr (ms_regs ms3) 10 = w64 (nx_hk (n_C cx) q) /\                                    (* a0 *)
  garr8 SEGS (rdW W3 (ms_mem ms3)) (nF cx fp + NO_PH) (nx_hdr (n_C cx) q) /\
  (* the registers *)
  getr (ms_regs ms3) 19 = w64 (nF cx fp + NO_PH) /\                                    (* s3 *)
  getr (ms_regs ms3) 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) /\      (* s4 *)
  (* the model: the turn started at q *)
  n_p cx <= q <= Z.of_nat (length (n_C cx)) /\
  nx_chain_inv (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) (n_p cx) q lh.

End c.
End b.
End a.

(* nx_hdra_inv names no sink head (asource_at takes none), so SK is not among its binders: its arguments are
   {fx} {rc} {PI} B MT KS, the loop measure R and the eight of a phase predicate. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (PI : PAImg pcap_listing) (B : asyms) (MT : ameter_ops)
  (KS : asource_syms) (R : ncx -> Z -> Prop) => @nx_hdra_inv fx rc PI B MT KS R).
