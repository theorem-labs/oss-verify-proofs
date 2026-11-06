(* lib/B/Prog/BoxBClose.v row 7 (H_STARTUP_B) at BB := TfibB (lib/B/AD2l.v), image fuzz_boxreg.asan-ubsan: every
   field of boxb_startup_B from the generated start-up data (lib/B/AF0m.v TFIB_ERRNO, lib/B/ACej.v Tfib_universe)
   and the image's segments. Row 8 (H_GSHADOW_B) is a Theorem Labs lane's lib/B/Prog/BoxBGShadow.v. The ROM-byte decision
   procedure is the B twin of a Theorem Labs lane's premise-audit one (lib/A, boxpa/premaudit-a/ZzPremAuditA2.v.txt).
   rule 24: no function proved (kind: start-up data facts). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop YK11 YM05 YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBImg BoxBAddr BoxBLibX BoxBCheck BoxBCloseDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require SnprintfDefB SnprintfBridgeB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require AD2l ACej.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BSNP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.SnprintfDefB.
Module BACej := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.ACej.
Notation TB := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.AD2l.TfibB.

(* ---- ROM bytes of boxb_segs at TfibB, decided ---- *)
Definition rb_in_rom_b (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) boxb_segs.
Definition rb_owned_b (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static TB).
Definition rb_errno_b (a : Z) : bool := (as_errno TB <=? a) && (a <? as_errno TB + 4).
Definition rb_byte_b (a v : Z) : bool :=
  match option_map (fun b : byte => bv_unsigned b) (seg_rom boxb_segs (Z_to_bv 64 a)) with
  | Some x => Z.eqb x v | None => false end.
Definition rb_some_b (a : Z) : bool := match seg_rom boxb_segs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition rb_rom_bytes_b (a : Z) (l : list Z) : bool :=
  forallb (fun i => rb_in_rom_b (a + i) && negb (rb_owned_b (a + i)) && negb (rb_errno_b (a + i)) &&
    rb_byte_b (a + i) (nth (Z.to_nat i) l 0)) (YG0n.zseq 0 (Z.of_nat (length l))).
Definition rb_tail_b (x k : Z) : bool :=
  forallb (fun a => rb_in_rom_b a && rb_some_b a) (YG0n.zseq (x + k + 1) (BSNP.absn_word_end x k - (x + k + 1))).

Lemma rb_in_zseq : forall lo n i, 0 <= i < n -> In (lo + i) (YG0n.zseq lo n).
Proof. intros lo n i H. unfold YG0n.zseq. apply in_map_iff. exists (Z.to_nat i). split; [lia | apply in_seq; lia]. Qed.
Lemma rb_in_rom_b_ok : forall a, rb_in_rom_b a = true -> in_rom boxb_segs a.
Proof.
intros a H. apply existsb_exists in H as (sg & Hin & Hb).
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
exists sg. split; [exact Hin | split; [exact H1 | lia]].
Qed.
Lemma rb_owned_b_false : forall a, rb_owned_b a = false -> ~ Exists (in_zr a) (as_owned_static TB).
Proof.
intros a H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (T : rb_owned_b a = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.
Lemma rb_rom_bytes_b_ok : forall a l, rb_rom_bytes_b a l = true -> BSNP.absn_rom_bytes boxb_segs TB a l.
Proof.
intros a l H i Hi.
pose proof (proj1 (forallb_forall _ _) H (0 + i) (rb_in_zseq 0 _ i Hi)) as Hb. cbv beta in Hb.
replace (0 + i) with i in Hb by lia.
apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply negb_true_iff in H2. apply negb_true_iff in H3.
split; [exact (rb_in_rom_b_ok _ H1)|]. split; [exact (rb_owned_b_false _ H2)|]. split.
- intros He. unfold rb_errno_b in H3.
  rewrite (proj2 (Z.leb_le _ _) (proj1 He)), (proj2 (Z.ltb_lt _ _) (proj2 He)) in H3. discriminate.
- unfold rb_byte_b in H4. destruct (option_map (fun b : byte => bv_unsigned b) (seg_rom boxb_segs (Z_to_bv 64 (a + i))))
    as [x|]; [|discriminate]. apply Z.eqb_eq in H4. rewrite H4. reflexivity.
Qed.
Lemma rb_tail_ok : forall x k, rb_tail_b x k = true ->
  forall a, x + k < a < BSNP.absn_word_end x k -> in_rom boxb_segs a /\ seg_rom boxb_segs (Z_to_bv 64 a) <> None.
Proof.
intros x k H a Ha.
assert (Hin : In a (YG0n.zseq (x + k + 1) (BSNP.absn_word_end x k - (x + k + 1)))).
{ replace a with ((x + k + 1) + (a - (x + k + 1))) at 1 by lia. apply rb_in_zseq. lia. }
pose proof (proj1 (forallb_forall _ _) H a Hin) as Hb. cbv beta in Hb.
apply andb_prop in Hb as [H1 H2]. split; [exact (rb_in_rom_b_ok a H1)|].
unfold rb_some_b in H2. destruct (seg_rom boxb_segs (Z_to_bv 64 a)); [discriminate | discriminate H2].
Qed.
Lemma rb_rom_str_nil_ok : forall x, rb_rom_bytes_b x [0] = true -> rb_tail_b x 0 = true ->
  BSNP.absn_rom_str boxb_segs TB x [].
Proof.
intros x H1 H2. split; [exact (rb_rom_bytes_b_ok x [0] H1)|].
exact (rb_tail_ok x (Z.of_nat (length (@nil Z))) H2).
Qed.

(* ---- the six fields ---- *)
Lemma boxb_stB_errno_TfibB : (0 <= as_errno TB /\ as_errno TB + 4 <= kLowMemEnd) /\
  (forall a, as_errno TB <= a < as_errno TB + 4 -> YG0d.in_img boxb_segs a).
Proof.
assert (E : as_errno TB = 0x5d42ac) by reflexivity. rewrite E.
split; [unfold kLowMemEnd; lia|].
intros a Ha. apply SnprintfBridgeB.boxb_img_cover_all.
assert (L : IMG_LO <= 0x5d42ac) by (vm_compute; discriminate).
assert (T : 0x5d42ac + 4 <= IMG_TOP) by (vm_compute; discriminate). lia.
Qed.

Lemma boxb_stB_uok_TfibB : universe_ok (as_universe TB).
Proof. exact BACej.Tfib_universe_ok. Qed.

Lemma boxb_stB_ra0_TfibB : In [pc_malloc_ra0 (as_code TB)] (as_universe TB) /\
  In [pc_free_ra0 (as_code TB)] (as_universe TB).
Proof. split; apply BACej.memZL_In; vm_compute; reflexivity. Qed.

Lemma boxb_stB_rn_TfibB : In [pc_malloc_ra0 (as_code TB); BOXB_RN_MALLOC_RA] (as_universe TB).
Proof. apply BACej.memZL_In. vm_compute. reflexivity. Qed.

(* The four allocator call sites of LLVMFuzzerTestOneInput, each with the empty chain and with the one frame whose
   return address is RAB_LLVMF: eight closed traces, all in Tfib_universe. *)
Lemma boxb_stB_htr_TfibB : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RAB_LLVMF ->
  (pcf = pc_malloc_ra0 (as_code TB) /\ In (raZ regsT - boxb_text) BOXB_MSITES) \/
  (pcf = pc_free_ra0 (as_code TB) /\ In (raZ regsT - boxb_text) BOXB_FSITES) ->
  In (call_trace0 pcf regsT (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
    (as_universe TB).
Proof.
intros ly regs regsT pcf Hra Hs.
assert (Hsite : (pcf = pc_malloc_ra0 (as_code TB) /\ raZ regsT = 0x80180) \/
  (pcf = pc_free_ra0 (as_code TB) /\ (raZ regsT = 0x808b8 \/ raZ regsT = 0x808f8 \/ raZ regsT = 0x80e5c))).
{ unfold BOXB_MSITES, BOXB_FSITES, boxb_text in Hs. cbn [In] in Hs.
  destruct Hs as [(-> & [H|[]]) | (-> & [H|[H|[H|[]]]])]; [left | right | right | right]; (split; [reflexivity|]); lia. }
destruct (spZ regs + 16 <? ly_top ly).
- rewrite call_trace_cons, Hra.
  destruct Hsite as [(-> & ->) | (-> & [-> | [-> | ->]])]; apply BACej.memZL_In; vm_compute; reflexivity.
- rewrite call_trace_nil.
  destruct Hsite as [(-> & ->) | (-> & [-> | [-> | ->]])]; apply BACej.memZL_In; vm_compute; reflexivity.
Qed.

Lemma boxb_stB_rom_TfibB : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  BSNP.absn_rom_bytes boxb_segs TB 0x20cc0 (map (fun b : byte => bv_unsigned b) Boxreg.zero6) /\
  BSNP.absn_rom_bytes boxb_segs TB 0x20d00 [0; 0x40; 0xab; 0; 0] /\
  BSNP.absn_rom_bytes boxb_segs TB 0x20d40 BSNP.ABSN_FMT /\
  BSNP.absn_rom_bytes boxb_segs TB MCH_LOB MCH_CONSTSB /\
  BSNP.absn_rom_str boxb_segs TB 0x20ce0 [] /\ BSNP.absn_rom_str boxb_segs TB 0x20d60 [].
Proof.
intros rc fx.
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; apply rb_rom_str_nil_ok; vm_compute; reflexivity.
Qed.

(* ---- BoxBClose.v row 7 at TfibB ---- *)
Theorem boxb_startup_TfibB : boxb_startup_B TB.
Proof.
constructor.
- exact boxb_stB_errno_TfibB.
- exact boxb_stB_uok_TfibB.
- exact boxb_stB_ra0_TfibB.
- exact boxb_stB_rn_TfibB.
- exact boxb_stB_htr_TfibB.
- exact boxb_stB_rom_TfibB.
Qed.
