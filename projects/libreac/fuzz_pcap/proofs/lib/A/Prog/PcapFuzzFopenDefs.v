(* The contract of libreac_fuzz_fopen (fuzz_pcap.asan v1.9.0, 0x80738) as a SHARED statement: it names no image
   and no listing. Every datum an image fixes is a parameter -- the segments, the function's entry, the
   "<fuzz-input>" literal, the two globals, and the read-only-image fact the strcmp wrapper's contract asks of the
   caller (roimg; on the ASan build lib/A instantiates it with that build's ro_img, which speaks about that
   build's bytes) -- so the asan-ubsan twin states the same contract over its own image.
   What stays a number is what the two builds share: libreac_fuzz_fopen is byte-identical on them modulo
   relocation, so its 32-byte frame, LIBREAC_FUZZ_FOPEN_STK (= AFMEMOPEN_STK), EV_FUZZ_FOPEN = 1 and the C
   library's SRC_FILE_BLOCK = 1304 are the same on both.
   This file Requires no uncommitted file: the walk (PcapFuzzFopen.v) is where the draft of another owner's
   statement is used. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0s YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0s YC5d PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFmemopenISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Its stack: the callee with the larger window is the fmemopen wrapper, entered (by the tail jump) at this
   function's own sp; the strcmp wrapper runs below the 32-byte frame in ESTACK, 32 + 4096 <= AFMEMOPEN_STK. *)
Definition LIBREAC_FUZZ_FOPEN_STK : Z := AFMEMOPEN_STK.
(* Its events: the one allocation of the fmemopen wrapper. *)
Definition EV_FUZZ_FOPEN : Z := 1.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section p.
Variable segs : list Segment.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* The only bytes this function's code and its strcmp call may change: its own 32-byte frame and the ESTACK below
   it, where the strcmp wrapper runs. *)
Definition FO_WIN (sp0 a : Z) : Prop := sp0 - 32 - ESTACK <= a < sp0.

Lemma mbyte_kept_lo : forall (W : world segs) (m m' : word -> option byte) sp0 a,
(forall x, 0 <= x < 2 ^ 64 -> ~ FO_WIN sp0 x -> aview segs (w_H W) m' x = aview segs (w_H W) m x) ->
alloc_ceiling <= sp0 - 32 - ESTACK -> 0 <= a < alloc_ceiling ->
mbyte segs (rdW W m') a = mbyte segs (rdW W m) a.
Proof.
intros W m m' sp0 a HK Hlo Ha. pose proof asan_consts as (CC & _).
apply (mbyte_of_aview segs). apply HK; unfold FO_WIN; lia.
Qed.

Lemma val_mem_kept : forall (W : world segs) (m m' : word -> option byte) sp0 a k v,
(forall x, 0 <= x < 2 ^ 64 -> ~ FO_WIN sp0 x -> aview segs (w_H W) m' x = aview segs (w_H W) m x) ->
alloc_ceiling <= sp0 - 32 - ESTACK -> 0 <= a -> a + Z.of_nat k <= alloc_ceiling ->
val_mem segs (rdW W m) a k v -> val_mem segs (rdW W m') a k v.
Proof.
intros W m m' sp0 a k v HK Hlo Ha Hak HV j Hj.
rewrite (mbyte_kept_lo W m m' sp0 (a + Z.of_nat j) HK Hlo ltac:(lia)). exact (HV j Hj).
Qed.

Lemma garr8_kept : forall (W : world segs) (m m' : word -> option byte) sp0 p l,
(forall x, 0 <= x < 2 ^ 64 -> ~ FO_WIN sp0 x -> aview segs (w_H W) m' x = aview segs (w_H W) m x) ->
alloc_ceiling <= sp0 - 32 - ESTACK -> 0 <= p -> p + Z.of_nat (length l) <= alloc_ceiling ->
garr8 segs (rdW W m) p l -> garr8 segs (rdW W m') p l.
Proof.
intros W m m' sp0 p l HK Hlo Hp Hpl HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
eapply (val_mem_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn [Z.of_nat]; lia | exact Hv].
Qed.

Lemma asource_none_kept : forall (K : asource_syms) (W : world segs) (m m' : word -> option byte) sp0,
Forall (fun a => 0 <= a /\ a + 16 <= pcap_img_end)
  [as_threaded K; as_need_locks K; as_ofl_lock K; as_mode K; as_rwa K; as_canary K] ->
(forall x, 0 <= x < 2 ^ 64 -> ~ FO_WIN sp0 x -> aview segs (w_H W) m' x = aview segs (w_H W) m x) ->
alloc_ceiling <= sp0 - 32 - ESTACK ->
asource_none segs K (rdW W m) -> asource_none segs K (rdW W m').
Proof.
intros K W m m' sp0 HKIMG HK Hlo ((Ht & Hn & Hl & Hmo & Hms & cv & Rcv & Hc) & Hh).
pose proof asan_consts as (CC & _).
pose proof (proj1 (Forall_forall _ _) HKIMG) as HI.
assert (HB1 : 0 <= as_threaded K /\ as_threaded K + 16 <= pcap_img_end) by (apply HI; cbn; tauto).
assert (HB2 : 0 <= as_need_locks K /\ as_need_locks K + 16 <= pcap_img_end) by (apply HI; cbn; tauto).
assert (HB3 : 0 <= as_ofl_lock K /\ as_ofl_lock K + 16 <= pcap_img_end) by (apply HI; cbn; tauto).
assert (HB4 : 0 <= as_mode K /\ as_mode K + 16 <= pcap_img_end) by (apply HI; cbn; tauto).
assert (HB6 : 0 <= as_rwa K /\ as_rwa K + 16 <= pcap_img_end) by (apply HI; cbn; tauto).
assert (HB5 : 0 <= as_canary K /\ as_canary K + 16 <= pcap_img_end) by (apply HI; cbn; tauto).
unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- eapply (val_mem_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn; lia | exact Ht].
- eapply (val_mem_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn; lia | exact Hn].
- eapply (val_mem_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn; lia | exact Hl].
- eapply (garr8_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn; lia | exact Hmo].
- eapply (garr8_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn; lia | exact Hms].
- exists cv. split; [exact Rcv|].
  eapply (val_mem_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn; lia | exact Hc].
- unfold as_ofl_head in *.
  eapply (val_mem_kept W m m' sp0); [exact HK | exact Hlo | lia | cbn; lia | exact Hh].
Qed.


Lemma md_fds_wvb : forall l x (m : Model), m_fds (with_vm_backing l x m) = m_fds m.
Proof. intros l x m. destruct m. reflexivity. Qed.
Lemma md_fs_wvb : forall l x (m : Model), m_fs (with_vm_backing l x m) = m_fs m.
Proof. intros l x m. destruct m. reflexivity. Qed.
Lemma sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. unfold same_but_materialized in H. rewrite H. split; [apply md_fds_wvb | apply md_fs_wvb]. Qed.

Lemma sv_off0 : forall (E0 : env) (k : nat) (v : word), ew E0 k = v -> sv_denot E0 (SOff k 0) = v.
Proof. intros E0 k v Hv. cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Definition tlibreac_fuzz_fopen_post (B : asyms) (K : asource_syms) (MT : ameter_ops)
  (regs : bvmap 5 word) ly S (W : world segs) mem md (n b : Z) (C : list Z)
  : world segs -> config -> Prop :=
apost_base (SK := SK) segs B LIBREAC_FUZZ_FOPEN_STK afmemopen_fp regs ly S W mem md EV_FUZZ_FOPEN
(fun ly' S' W' regs' mem' md' => exists h : Z,
  getr regs' 10 = w64 h /\ frames S' = frames S /\
  (* no descriptor and no file-system change *)
  m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
  (* the empty input (0x8078c): NULL, no block and no stream *)
  (n = 0 -> h = 0 /\ ablocks B ly' S' = ablocks B ly S /\ asource_none segs K (rdW W' mem') /\ mo_le MT S S' 0) /\
  (* otherwise the fmemopen wrapper opened the stream on the harness's buffer *)
  (1 <= n -> 4096 <= h /\ h mod 16 = 0 /\ ablocks B ly' S' = ablocks B ly S ++ [(h, SRC_FILE_BLOCK)] /\
     asource_unbuffered segs K (rdW W' mem') h b C 0 /\ mo_le MT S S' (mo_malloc MT SRC_FILE_BLOCK))).

Definition tlibreac_fuzz_fopen_specX (A_FOPEN A_PATH A_GLEN A_GFILE : Z)
  (roimg : (word -> option byte) -> Prop)
  (B : asyms) (K : asource_syms) (MT : ameter_ops) (FM_RA : Z) (CTX : list (list Z)) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (n b : Z) (C : list Z),
afn_pre segs B LIBREAC_FUZZ_FOPEN_STK ly S W regs mem md ch ->
In (spine ch) CTX ->
getr regs 10 = w64 (A_PATH) -> getr regs 11 = w64 (as_mode K) ->
roimg (rdW W mem) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (A_PATH) 13 ->
shadow_hull_vis (aview segs (w_H W) mem) (A_PATH) 13 ->
val_mem segs (rdW W mem) (A_GLEN) 8 n -> val_mem segs (rdW W mem) (A_GFILE) 8 b ->
0 <= b < 2 ^ 64 ->
asource_none segs K (rdW W mem) ->
n = Z.of_nat (length C) -> n < 2 ^ 26 ->
(1 <= n -> In (b, n) (ablocks B ly S) /\ garr8 segs (rdW W mem) b C /\ bytes_ok C) ->
st_nev S + EV_FUZZ_FOPEN <= EV_MAX -> blocks_bytes S + SRC_FILE_BLOCK <= LIVE_MAX ->
mo_ok MT S (mo_malloc MT SRC_FILE_BLOCK) ->
In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
(forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
   flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)) ->
SRr segs W (cfg_at segs A_FOPEN regs mem md) (tlibreac_fuzz_fopen_post B K MT regs ly S W mem md n b C).

End p.
End d.
Arguments tlibreac_fuzz_fopen_post {fx rc} SK segs B K MT regs ly S W mem md n b C _ _.
Arguments tlibreac_fuzz_fopen_specX {fx rc} SK segs A_FOPEN A_PATH A_GLEN A_GFILE roimg B K MT FM_RA CTX.

(* The guard: this fails to typecheck if SK or an image datum ever becomes implicit again. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment)
           (A_FOPEN A_PATH A_GLEN A_GFILE : Z) (roimg : (word -> option byte) -> Prop)
           (B : asyms) (K : asource_syms) (MT : ameter_ops) (FM_RA : Z) (CTX : list (list Z)) =>
         tlibreac_fuzz_fopen_specX (fx := fx) (rc := rc) SK segs A_FOPEN A_PATH A_GLEN A_GFILE roimg
           B K MT FM_RA CTX).
