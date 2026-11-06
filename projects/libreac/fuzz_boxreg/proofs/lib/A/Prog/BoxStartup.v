(* lib/A/Prog/BoxClose.v row 7 (H_STARTUP_A) at BA := TfibB (lib/A/AD2l.v), image fuzz_boxreg.asan: every field of
   box_startup_A from the generated start-up data (lib/A/AF0m.v TFIB_ERRNO, lib/A/ACej.v Tfib_universe) and the image's
   segments. The A twin of lib/B/Prog/BoxBStartup.v. Row 8 (H_GSHADOW_A) is a Theorem Labs lane's lib/A/Prog/BoxGShadow.v. The
   ROM-byte decision procedure is a Theorem Labs lane's premise-audit one (boxpa/premaudit-a/ZzPremAuditA2.v.txt).
   rule 24: no function proved (kind: start-up data facts). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop YK11 YM05 YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxImg BoxAddr BoxLibX Check BoxCloseDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef SnprintfBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require AD2l ACej.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module ASNP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.SnprintfDef.
Module AACej := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.ACej.
Notation TA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AD2l.TfibB.

(* ---- ROM bytes of box_segs at TfibB, decided ---- *)
Definition rb_in_rom_b (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) box_segs.
Definition rb_owned_b (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static TA).
Definition rb_errno_b (a : Z) : bool := (as_errno TA <=? a) && (a <? as_errno TA + 4).
Definition rb_byte_b (a v : Z) : bool :=
  match option_map (fun b : byte => bv_unsigned b) (seg_rom box_segs (Z_to_bv 64 a)) with
  | Some x => Z.eqb x v | None => false end.
Definition rb_some_b (a : Z) : bool := match seg_rom box_segs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition rb_rom_bytes_b (a : Z) (l : list Z) : bool :=
  forallb (fun i => rb_in_rom_b (a + i) && negb (rb_owned_b (a + i)) && negb (rb_errno_b (a + i)) &&
    rb_byte_b (a + i) (nth (Z.to_nat i) l 0)) (YG0n.zseq 0 (Z.of_nat (length l))).
Definition rb_tail_b (x k : Z) : bool :=
  forallb (fun a => rb_in_rom_b a && rb_some_b a) (YG0n.zseq (x + k + 1) (ASNP.asn_word_end x k - (x + k + 1))).

Lemma rb_in_zseq : forall lo n i, 0 <= i < n -> In (lo + i) (YG0n.zseq lo n).
Proof. intros lo n i H. unfold YG0n.zseq. apply in_map_iff. exists (Z.to_nat i). split; [lia | apply in_seq; lia]. Qed.
Lemma rb_in_rom_b_ok : forall a, rb_in_rom_b a = true -> in_rom box_segs a.
Proof.
intros a H. apply existsb_exists in H as (sg & Hin & Hb).
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
exists sg. split; [exact Hin | split; [exact H1 | lia]].
Qed.
Lemma rb_owned_b_false : forall a, rb_owned_b a = false -> ~ Exists (in_zr a) (as_owned_static TA).
Proof.
intros a H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (T : rb_owned_b a = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.
Lemma rb_rom_bytes_b_ok : forall a l, rb_rom_bytes_b a l = true -> ASNP.asn_rom_bytes box_segs TA a l.
Proof.
intros a l H i Hi.
pose proof (proj1 (forallb_forall _ _) H (0 + i) (rb_in_zseq 0 _ i Hi)) as Hb. cbv beta in Hb.
replace (0 + i) with i in Hb by lia.
apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply negb_true_iff in H2. apply negb_true_iff in H3.
split; [exact (rb_in_rom_b_ok _ H1)|]. split; [exact (rb_owned_b_false _ H2)|]. split.
- intros He. unfold rb_errno_b in H3.
  rewrite (proj2 (Z.leb_le _ _) (proj1 He)), (proj2 (Z.ltb_lt _ _) (proj2 He)) in H3. discriminate.
- unfold rb_byte_b in H4. destruct (option_map (fun b : byte => bv_unsigned b) (seg_rom box_segs (Z_to_bv 64 (a + i))))
    as [x|]; [|discriminate]. apply Z.eqb_eq in H4. rewrite H4. reflexivity.
Qed.
Lemma rb_tail_ok : forall x k, rb_tail_b x k = true ->
  forall a, x + k < a < ASNP.asn_word_end x k -> in_rom box_segs a /\ seg_rom box_segs (Z_to_bv 64 a) <> None.
Proof.
intros x k H a Ha.
assert (Hin : In a (YG0n.zseq (x + k + 1) (ASNP.asn_word_end x k - (x + k + 1)))).
{ replace a with ((x + k + 1) + (a - (x + k + 1))) at 1 by lia. apply rb_in_zseq. lia. }
pose proof (proj1 (forallb_forall _ _) H a Hin) as Hb. cbv beta in Hb.
apply andb_prop in Hb as [H1 H2]. split; [exact (rb_in_rom_b_ok a H1)|].
unfold rb_some_b in H2. destruct (seg_rom box_segs (Z_to_bv 64 a)); [discriminate | discriminate H2].
Qed.
Lemma rb_rom_str_nil_ok : forall x, rb_rom_bytes_b x [0] = true -> rb_tail_b x 0 = true ->
  ASNP.asn_rom_str box_segs TA x [].
Proof.
intros x H1 H2. split; [exact (rb_rom_bytes_b_ok x [0] H1)|].
exact (rb_tail_ok x (Z.of_nat (length (@nil Z))) H2).
Qed.

(* ---- the six fields ---- *)
Lemma box_stA_errno_TfibB : (0 <= as_errno TA /\ as_errno TA + 4 <= kLowMemEnd) /\
  (forall a, as_errno TA <= a < as_errno TA + 4 -> YG0d.in_img box_segs a).
Proof.
assert (E : as_errno TA = 0x5d3e6c) by reflexivity. rewrite E.
split; [unfold kLowMemEnd; lia|].
intros a Ha. apply SnprintfBridge.box_img_cover_all.
assert (L : IMG_LO <= 0x5d3e6c) by (vm_compute; discriminate).
assert (T : 0x5d3e6c + 4 <= IMG_TOP) by (vm_compute; discriminate). lia.
Qed.

Lemma box_stA_uok_TfibB : universe_ok (as_universe TA).
Proof. exact AACej.Tfib_universe_ok. Qed.

Lemma box_stA_ra0_TfibB : In [pc_malloc_ra0 (as_code TA)] (as_universe TA) /\
  In [pc_free_ra0 (as_code TA)] (as_universe TA).
Proof. split; apply AACej.memZL_In; vm_compute; reflexivity. Qed.

Lemma box_stA_rn_TfibB : In [pc_malloc_ra0 (as_code TA); BOX_RN_MALLOC_RA] (as_universe TA).
Proof. apply AACej.memZL_In. vm_compute. reflexivity. Qed.

(* The four allocator call sites of LLVMFuzzerTestOneInput, each with the empty chain and with the one frame whose
   return address is RA_LLVMF: eight closed traces, all in Tfib_universe. *)
Lemma box_stA_htr_TfibB : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RA_LLVMF ->
  (pcf = pc_malloc_ra0 (as_code TA) /\ In (raZ regsT - box_text) BOX_MSITES) \/
  (pcf = pc_free_ra0 (as_code TA) /\ In (raZ regsT - box_text) BOX_FSITES) ->
  In (call_trace0 pcf regsT (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
    (as_universe TA).
Proof.
intros ly regs regsT pcf Hra Hs.
assert (Hsite : (pcf = pc_malloc_ra0 (as_code TA) /\ raZ regsT = 0x8011c) \/
  (pcf = pc_free_ra0 (as_code TA) /\ (raZ regsT = 0x80600 \/ raZ regsT = 0x80aac \/ raZ regsT = 0x80e1c))).
{ unfold BOX_MSITES, BOX_FSITES, box_text in Hs. cbn [In] in Hs.
  destruct Hs as [(-> & [H|[]]) | (-> & [H|[H|[H|[]]]])]; [left | right | right | right]; (split; [reflexivity|]); lia. }
destruct (spZ regs + 16 <? ly_top ly).
- rewrite call_trace_cons, Hra.
  destruct Hsite as [(-> & ->) | (-> & [-> | [-> | ->]])]; apply AACej.memZL_In; vm_compute; reflexivity.
- rewrite call_trace_nil.
  destruct Hsite as [(-> & ->) | (-> & [-> | [-> | ->]])]; apply AACej.memZL_In; vm_compute; reflexivity.
Qed.

Lemma box_stA_rom_TfibB : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  ASNP.asn_rom_bytes box_segs TA 0x20cc0 (map (fun b : byte => bv_unsigned b) Boxreg.zero6) /\
  ASNP.asn_rom_bytes box_segs TA 0x20d00 [0; 0x40; 0xab; 0; 0] /\
  ASNP.asn_rom_bytes box_segs TA 0x20d40 ASNP.ASN_FMT /\
  ASNP.asn_rom_bytes box_segs TA MCH_LO MCH_CONSTS /\
  ASNP.asn_rom_str box_segs TA 0x20ce0 [] /\ ASNP.asn_rom_str box_segs TA 0x20d60 [].
Proof.
intros rc fx.
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; [apply rb_rom_bytes_b_ok; vm_compute; reflexivity|].
split; apply rb_rom_str_nil_ok; vm_compute; reflexivity.
Qed.

(* ---- BoxClose.v row 7 at TfibB (the record and constants are in BoxCloseDefs.v, which BoxClose.v Require Exports) ---- *)
Theorem box_startup_TfibB : box_startup_A TA.
Proof.
constructor.
- exact box_stA_errno_TfibB.
- exact box_stA_uok_TfibB.
- exact box_stA_ra0_TfibB.
- exact box_stA_rn_TfibB.
- exact box_stA_htr_TfibB.
- exact box_stA_rom_TfibB.
Qed.
