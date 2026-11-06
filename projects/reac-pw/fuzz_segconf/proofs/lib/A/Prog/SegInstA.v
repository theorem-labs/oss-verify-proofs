(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan, pin sha256 48c5355bdacb..., twin 4362701197e4...): the one
   image-A instantiation of the parameters of segconf's ASan-level function contracts (lib/A/Prog/<F>_c.v). A walk
   theorem of F and every caller's hypothesis about F use these terms, so the close needs no bridge between two
   spellings of one number.
   proves no function (kind: instantiation: definitions, and lemmas closed by computation that tie each value to
   the listing (SegAddr, SegList) or to the image's bytes (images/Asan.v)).
   Owner: the image-A owner (the close lane). Folded in: the G3 walk lane's interim lib/A/Prog/SegG3Inst.v
   (commit ab4c0db8d074): its STK_ texts, its reac_segconf.c literal table with the pcs that form
   each address, catA, gotwA, guardA and their lemma names. Its seg_litA is seg_litA_rc here (two maps, below).

   WHERE EACH VALUE COMES FROM (no number is restated that another file states):
   - A_<F>_A, F's entry: SegAddr.seg_sigma SS_<F> (the listing's call targets, each equal to the twin's .symtab
     address of F, checked 2026-10-30); LLVMFuzzerTestOneInput's is SegAddr.seg_text. A_<F>_A_AF ties each to
     SegList's position-abstract AF_<F> (a walk under PAImg names F as BASE + AF_<F>, BASE = seg_text for PB_seg).
   - RLO_A / RHI_A: SegGlob.SEG_RLO / SEG_RHI (.data.rel.ro start, .got end). longlA: SegGlob.A_LONGL.
   - pc_memsetA, pc_memcpyA, the trampolines pc_<x>A, the side-stack entries, the shadow fills and musl isalnum:
     SegAddr.seg_sigma. pc_segi ties the nine entries the interceptor lane's lib/A/Rt/SegRtPC.v names to them, pc_rtapi
     the eleven entries and the two stack-protector cells the core's lib/A/Rt/RtAPI.v names.
   - Walks state entries and call targets as listing terms under `Context {PI : PAImg seg_listing}` (pa_val A_TEXT
     + AF_<F>, pa_sigma SS_<x>) and take only the pure parameters from here (the image-A owner's ruling, 2026-10-30). The
     close rewrites them to A_<F>_A / pc_<x>A at image A's instance SegImg.PB_seg (the core's AB1v is needed to
     build SegImg), by the close's lemmas; A_<F>_A_AF and the pc_<x>A definitions are this file's half.
   - The numbers stated here, each with its check: catA 0xa18e0 (twin .symtab fuzz_catalogue; catA_rows reads
     the 11 token rows in the image), wordsA 0xa1880 / rolesA 0x211e0 (.symtab m_key.words / m_key.role, the
     harness's and m_file's WORDS / ROLES; wordsA_rows, rolesA_rows read them in the image), gotwA 0xa36d8 /
     guardA 0x5ff078 (.got word, .symtab __stack_chk_guard; gotwA_img reads the word in the image), mod40A
     0x103c8 (mod40A_img: the image's 8 bytes are LTOI_MOD40), emptyA 0x5de660 (twin .symtab
     oft_aligned_copy.empty, 32 bytes: the driver's object for an empty payload; fuzz_command's A_EMPTY 0x5e3720
     is the same symbol of its image), memchr_loA / memchr_hiA 0x10350 / 0x10370 (musl's word-loop constants;
     memchr_code reads the loads in musl memchr, memchr_win_img the two words, memchr_win_rom the segment).
   - STK_<F> for all 34: the walk groups' measurements (the stack tables of the G1, G2 and G4 / G5 walk lanes,
     and the G3 walk lane's SegG3Inst.v), written as F's frame plus the
     deepest window below it, so that a callee's window enters its caller's by name; STK_values gives the numbers.
   - THE LITERALS: two maps. 18 texts are in the image twice, one global per translation unit (twin
     asan_globals, module column): "%s" 0x21080 / 0x21340, "reac-pw.conf" 0x210a0 / 0x21360, "%s:%d: " 0x210c0 /
     0x21aa0, "%s: " 0x210e0 / 0x21ac0, and segment, role, auto, master, slave, tap, box, model, ignore, yes, true,
     no, false, knock at 0x21100..0x212e0 (fuzz_segconf.c) and 0x214a0..0x21be0 (reac_segconf.c). sa_lit asks
     the literal's shadow and ROM tail at `lit s`, so each walk needs lit s = the address its code forms.
     seg_litA_fz is fuzz_segconf.c's map, over LLVMFuzzerTestOneInput_c.LTOI_FZ_LITS (the harness's own texts,
     check_knock_refused's, m_refuse's and m_file's). seg_litA_rc is
     reac_segconf.c's map, over LTOI_RC_LITS (reac_segconf_parse_file's and cross_check's lists, which hold
     refuse's; reac_segconf_parse takes these two). Each contract keeps its own `lit`; its instantiation takes
     its module's map. For every text of both lists, seg_litA_fz_facts / seg_litA_rc_facts give: a positive
     address, an object of the listing, the image's bytes there are the text and its NUL, the ROM tail
     (SegABase.sa_romtail over the image's segments, so the contracts' sa_romtail premise is discharged here),
     and the literal ends below longl. The shadow half of sa_lit (sa_pinned) is the listing's
     SegRecBase.seg_lit_pinned over its seg_lit_objs; SEG_LIT_OBJS_A lists this file's (address, size) pairs
     for that join. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_segconf.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YK11 YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require LLVMFuzzerTestOneInput_c refuse_c
cross_check_c reac_segconf_parse_file_c check_knock_refused_c m_refuse_c m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegAddr SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require SegRtPC RtAPI.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================================== the image's bytes ===================================== *)
(* the image's byte at a (the ROM byte of images/Asan.v's segments, as SegABase.sa_romtail and RtDefs read it) *)
Definition img_rd (a : Z) : option Z :=
option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom Asan.M.loaded_segments (Z_to_bv 64 a)).
(* the image holds the bytes l from a *)
Fixpoint img_bytes_b (a : Z) (l : list Z) : bool :=
match l with
| [] => true
| x :: r => match img_rd a with Some v => Z.eqb v x | None => false end && img_bytes_b (a + 1) r
end.
Lemma img_bytes_b_ok : forall l a, img_bytes_b a l = true ->
forall i, (i < length l)%nat -> img_rd (a + Z.of_nat i) = Some (nth i l 0).
Proof.
induction l as [|x l IH]; intros a H i Hi; cbn [length] in Hi; [lia|].
cbn [img_bytes_b] in H. apply andb_prop in H as [H1 H2].
destruct i as [|i].
- cbn [nth]. replace (a + Z.of_nat 0) with a by lia. destruct (img_rd a) as [v|]; [|discriminate H1].
  apply Z.eqb_eq in H1. rewrite H1. reflexivity.
- cbn [nth]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia. apply IH; [exact H2 | lia].
Qed.
(* the little-endian value of the image's n bytes from a *)
Fixpoint img_le (a : Z) (n : nat) : option Z :=
match n with
| O => Some 0
| S n' => match img_rd a, img_le (a + 1) n' with Some v, Some w => Some (v + 256 * w) | _, _ => None end
end.
(* f holds at lo, lo + 1, ..., lo + k - 1 *)
Fixpoint all_from (f : Z -> bool) (lo : Z) (k : nat) : bool :=
match k with O => true | S k' => f lo && all_from f (lo + 1) k' end.
Lemma all_from_ok : forall f k lo, all_from f lo k = true -> forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
intros f k. induction k as [|k IH]; intros lo H x Hx; cbn [all_from] in H; [lia|].
apply andb_prop in H as [H1 H2]. destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.
(* the image has a ROM byte at x *)
Definition rom_some_b (x : Z) : bool :=
match YK11.seg_rom Asan.M.loaded_segments (Z_to_bv 64 x) with Some _ => true | None => false end.
(* the bytes after e up to the end of e's 8-byte word have ROM bytes (SegABase.sa_romtail) *)
Definition romtail_b (e : Z) : bool := all_from rom_some_b (e + 1) (Z.to_nat (7 - e mod 8)).
Lemma romtail_b_ok : forall e, romtail_b e = true -> SegABase.sa_romtail Asan.M.loaded_segments e.
Proof.
intros e H x Hx. unfold romtail_b in H. pose proof (all_from_ok _ _ _ H x) as Hf.
assert (Hm : 0 <= e mod 8 < 8) by (apply Z.mod_pos_bound; lia).
unfold rom_some_b in Hf. destruct (YK11.seg_rom Asan.M.loaded_segments (Z_to_bv 64 x)); [discriminate|].
exfalso. assert (false = true) by (apply Hf; rewrite Z2Nat.id by lia; lia). discriminate.
Qed.
(* a ROM tail is a mapped tail of the image reader *)
Lemma romtail_img_tail : forall e, SegABase.sa_romtail Asan.M.loaded_segments e -> SegABase.sa_tail img_rd e.
Proof.
intros e H x Hx. specialize (H x Hx). unfold img_rd.
destruct (YK11.seg_rom Asan.M.loaded_segments (Z_to_bv 64 x)); [discriminate | exfalso; exact (H eq_refl)].
Qed.
Lemma nonul_ok : forall s, negb (existsb (Z.eqb 0) s) = true -> ~ In 0 s.
Proof.
intros s H Hin. apply negb_true_iff in H.
assert (existsb (Z.eqb 0) s = true) by (apply existsb_exists; exists 0; split; [exact Hin | apply Z.eqb_refl]).
congruence.
Qed.
(* the image's word at a points to the C string s: positive, s and its NUL there, no NUL inside s, its ROM tail *)
Definition ptr_str_okb (a : Z) (s : list Z) : bool :=
match YG0d.rdword img_rd a with
| Some p => (0 <? p) && img_bytes_b p (s ++ [0]) && negb (existsb (Z.eqb 0) s) && romtail_b (p + Z.of_nat (length s))
| None => false
end.
Lemma ptr_str_okb_ok : forall a s, ptr_str_okb a s = true ->
  exists p, YG0d.rdword img_rd a = Some p /\ 0 < p /\ SegABase.sa_str img_rd p s /\
    SegABase.sa_romtail Asan.M.loaded_segments (p + Z.of_nat (length s)).
Proof.
intros a s H. unfold ptr_str_okb in H. destruct (YG0d.rdword img_rd a) as [p|]; [|discriminate H].
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
exists p. split; [reflexivity|]. split; [apply Z.ltb_lt; exact H1|].
split; [|exact (romtail_b_ok _ H4)].
split; [split; [exact (img_bytes_b_ok _ _ H2) | exact (nonul_ok _ H3)] | exact (romtail_img_tail _ (romtail_b_ok _ H4))].
Qed.

(* ===================================== the entries ===================================== *)
Definition A_LLVMFuzzerTestOneInput_A : Z := seg_text.
Definition A_m_file_A : Z := seg_sigma SS_m_file.
Definition A_check_segments_A : Z := seg_sigma SS_check_segments.
Definition A_check_role_A : Z := seg_sigma SS_check_role.
Definition A_check_model_A : Z := seg_sigma SS_check_model.
Definition A_check_ignore_A : Z := seg_sigma SS_check_ignore.
Definition A_check_provenance_A : Z := seg_sigma SS_check_provenance.
Definition A_check_refusals_A : Z := seg_sigma SS_check_refusals.
Definition A_check_address_A : Z := seg_sigma SS_check_address.
Definition A_check_knock_refused_A : Z := seg_sigma SS_check_knock_refused.
Definition A_m_find_A : Z := seg_sigma SS_m_find.
Definition A_check_absent_A : Z := seg_sigma SS_check_absent.
Definition A_check_declared_A : Z := seg_sigma SS_check_declared.
Definition A_m_refuse_A : Z := seg_sigma SS_m_refuse.
Definition A_ieq_A : Z := seg_sigma SS_ieq.
Definition A_reac_segconf_init_A : Z := seg_sigma SS_reac_segconf_init.
Definition A_reac_segconf_parse_file_A : Z := seg_sigma SS_reac_segconf_parse_file.
Definition A_refuse_A : Z := seg_sigma SS_refuse.
Definition A_trim_A : Z := seg_sigma SS_trim.
Definition A_reac_segconf_parse_A : Z := seg_sigma SS_reac_segconf_parse.
Definition A_cross_check_A : Z := seg_sigma SS_cross_check.
Definition A_reac_segconf_find_A : Z := seg_sigma SS_reac_segconf_find.
Definition A_reac_segconf_ignored_A : Z := seg_sigma SS_reac_segconf_ignored.
Definition A_reac_segconf_role_A : Z := seg_sigma SS_reac_segconf_role.
Definition A_reac_segconf_role_file_A : Z := seg_sigma SS_reac_segconf_role_file.
Definition A_reac_segconf_ignore_file_A : Z := seg_sigma SS_reac_segconf_ignore_file.
Definition A_reac_segconf_model_A : Z := seg_sigma SS_reac_segconf_model.
Definition A_reac_segconf_declared_A : Z := seg_sigma SS_reac_segconf_declared.
Definition A_reac_declared_vlan_split_A : Z := seg_sigma SS_reac_declared_vlan_split.
Definition A_name_ok_A : Z := seg_sigma SS_name_ok.
Definition A_reac_declared_vlan_add_A : Z := seg_sigma SS_reac_declared_vlan_add.
Definition A_fuzz_catalogue_row_A : Z := seg_sigma SS_fuzz_catalogue_row.
Definition A_reac_box_catalogue_A : Z := seg_sigma SS_reac_box_catalogue.
Definition A_reac_box_catalogue_by_token_A : Z := seg_sigma SS_reac_box_catalogue_by_token.
Lemma A_LLVMFuzzerTestOneInput_A_AF : A_LLVMFuzzerTestOneInput_A = seg_text + AF_LLVMFuzzerTestOneInput.
Proof. vm_compute. reflexivity. Qed.
Lemma A_m_file_A_AF : A_m_file_A = seg_text + AF_m_file. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_segments_A_AF : A_check_segments_A = seg_text + AF_check_segments. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_role_A_AF : A_check_role_A = seg_text + AF_check_role. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_model_A_AF : A_check_model_A = seg_text + AF_check_model. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_ignore_A_AF : A_check_ignore_A = seg_text + AF_check_ignore. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_provenance_A_AF : A_check_provenance_A = seg_text + AF_check_provenance. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_refusals_A_AF : A_check_refusals_A = seg_text + AF_check_refusals. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_address_A_AF : A_check_address_A = seg_text + AF_check_address. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_knock_refused_A_AF : A_check_knock_refused_A = seg_text + AF_check_knock_refused. Proof. vm_compute. reflexivity. Qed.
Lemma A_m_find_A_AF : A_m_find_A = seg_text + AF_m_find. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_absent_A_AF : A_check_absent_A = seg_text + AF_check_absent. Proof. vm_compute. reflexivity. Qed.
Lemma A_check_declared_A_AF : A_check_declared_A = seg_text + AF_check_declared. Proof. vm_compute. reflexivity. Qed.
Lemma A_m_refuse_A_AF : A_m_refuse_A = seg_text + AF_m_refuse. Proof. vm_compute. reflexivity. Qed.
Lemma A_ieq_A_AF : A_ieq_A = seg_text + AF_ieq. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_init_A_AF : A_reac_segconf_init_A = seg_text + AF_reac_segconf_init. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_parse_file_A_AF : A_reac_segconf_parse_file_A = seg_text + AF_reac_segconf_parse_file. Proof. vm_compute. reflexivity. Qed.
Lemma A_refuse_A_AF : A_refuse_A = seg_text + AF_refuse. Proof. vm_compute. reflexivity. Qed.
Lemma A_trim_A_AF : A_trim_A = seg_text + AF_trim. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_parse_A_AF : A_reac_segconf_parse_A = seg_text + AF_reac_segconf_parse. Proof. vm_compute. reflexivity. Qed.
Lemma A_cross_check_A_AF : A_cross_check_A = seg_text + AF_cross_check. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_find_A_AF : A_reac_segconf_find_A = seg_text + AF_reac_segconf_find. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_ignored_A_AF : A_reac_segconf_ignored_A = seg_text + AF_reac_segconf_ignored. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_role_A_AF : A_reac_segconf_role_A = seg_text + AF_reac_segconf_role. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_role_file_A_AF : A_reac_segconf_role_file_A = seg_text + AF_reac_segconf_role_file. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_ignore_file_A_AF : A_reac_segconf_ignore_file_A = seg_text + AF_reac_segconf_ignore_file. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_model_A_AF : A_reac_segconf_model_A = seg_text + AF_reac_segconf_model. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_segconf_declared_A_AF : A_reac_segconf_declared_A = seg_text + AF_reac_segconf_declared. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_declared_vlan_split_A_AF : A_reac_declared_vlan_split_A = seg_text + AF_reac_declared_vlan_split. Proof. vm_compute. reflexivity. Qed.
Lemma A_name_ok_A_AF : A_name_ok_A = seg_text + AF_name_ok. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_declared_vlan_add_A_AF : A_reac_declared_vlan_add_A = seg_text + AF_reac_declared_vlan_add. Proof. vm_compute. reflexivity. Qed.
Lemma A_fuzz_catalogue_row_A_AF : A_fuzz_catalogue_row_A = seg_text + AF_fuzz_catalogue_row. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_box_catalogue_A_AF : A_reac_box_catalogue_A = seg_text + AF_reac_box_catalogue. Proof. vm_compute. reflexivity. Qed.
Lemma A_reac_box_catalogue_by_token_A_AF : A_reac_box_catalogue_by_token_A = seg_text + AF_reac_box_catalogue_by_token. Proof. vm_compute. reflexivity. Qed.

(* ======================================= image cells ======================================= *)
(* the read-only window of arodata_okP *)
Definition RLO_A : Z := SEG_RLO.
Definition RHI_A : Z := SEG_RHI.
Lemma RLO_A_seg : RLO_A = SEG_RLO. Proof. reflexivity. Qed.
Lemma RHI_A_seg : RHI_A = SEG_RHI. Proof. reflexivity. Qed.
(* the harness's .bss label LLVMFuzzerTestOneInput.longl (121 bytes) *)
Definition longlA : Z := A_LONGL.
(* the driver's object for an empty payload (twin .symtab oft_aligned_copy.empty, 32 bytes in .bss), apart from
   longl *)
Definition emptyA : Z := 0x5de660.
Lemma emptyA_apart_longl : emptyA + 32 <= longlA.
Proof. unfold emptyA, longlA, A_LONGL. lia. Qed.
(* longl's tail: the bytes after longl[120] to the end of its 8-byte word (0x5de6f9 .. 0x5de6ff, .bss) have image
   bytes, as the harness contract's seg_himg asks (sa_romtail (LONGL + LONGL_W)); the pin half (sa_pinned LONGL
   LONGL_N) is a record fact, the listing's SegRecBase *)
Lemma longlA_romtail : SegABase.sa_romtail Asan.M.loaded_segments (longlA + LLVMFuzzerTestOneInput_c.LONGL_W).
Proof. apply romtail_b_ok. vm_compute. reflexivity. Qed.
(* the multiplier cell of cap = u8 % 40 (.rodata; loaded at 0x84ed4 / 0x84ed8 with no instrumented check) *)
Definition mod40A : Z := 0x103c8.
Lemma mod40A_obj : In mod40A seg_objs.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma mod40A_img : img_le mod40A 8 = Some LLVMFuzzerTestOneInput_c.LTOI_MOD40.
Proof. vm_compute. reflexivity. Qed.
(* the same, as a reader fact over the image reader *)
Lemma img_mod40 : SegABase.sa_val img_rd mod40A 8 LLVMFuzzerTestOneInput_c.LTOI_MOD40.
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
(* the box-model table fuzz_catalogue (catalogue.c; .data.rel.ro): an object of the listing, inside the read-only
   window, and each of its 11 rows holds a pointer to its token, the token's bytes and NUL in the image, and the
   token's ROM tail (sa_cat's sa_lit at the pointer) *)
Definition catA : Z := 0xa18e0.
Lemma catA_obj : In catA seg_objs.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma catA_ro : RLO_A <= catA /\ catA + pin_spec.CAT_BYTES <= RHI_A.
Proof. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, catA, pin_spec.CAT_BYTES. lia. Qed.
Definition cat_row_okb (i : nat) : bool :=
ptr_str_okb (pin_spec.row_addr catA i) (seg_spec.zs (pin_spec.tok_bytes i)).
Lemma catA_rows : forallb cat_row_okb (seq 0 pin_spec.CAT_N) = true.
Proof. vm_compute. reflexivity. Qed.
(* the same, as reader facts over the image reader (sa_cat's rows) *)
Lemma img_cat_rows : forall i, (i < pin_spec.CAT_N)%nat ->
  exists tp, YG0d.rdword img_rd (pin_spec.row_addr catA i) = Some tp /\ 0 < tp /\
    SegABase.sa_str img_rd tp (seg_spec.zs (pin_spec.tok_bytes i)) /\
    SegABase.sa_romtail Asan.M.loaded_segments (tp + Z.of_nat (length (seg_spec.zs (pin_spec.tok_bytes i)))).
Proof.
intros i Hi. apply ptr_str_okb_ok. exact (proj1 (forallb_forall _ _) catA_rows i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))).
Qed.
(* m_key.words (fuzz_segconf.c; .data.rel.ro, 40 bytes, five pointers; formed at 0x86090) and m_key.role
   (.rodata, 20 bytes; formed at 0x86738 / 0x868b8), the harness's WORDS / ROLES and m_file's (m_file_c.mf_words /
   mf_roles): objects of the listing; word i points to m_file_c.MF_ROLE_WORDS's text i, its bytes and NUL in the
   image, with its ROM tail; entry i of m_key.role is i *)
Definition wordsA : Z := 0xa1880.
Definition rolesA : Z := 0x211e0.
Lemma wordsA_obj : In wordsA seg_objs.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma rolesA_obj : In rolesA seg_objs.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma wordsA_ro : RLO_A <= wordsA /\ wordsA + 40 <= RHI_A.
Proof. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, wordsA. lia. Qed.
Definition word_row_okb (i : nat) : bool :=
ptr_str_okb (wordsA + 8 * Z.of_nat i) (nth i m_file_c.MF_ROLE_WORDS []).
Lemma wordsA_rows : forallb word_row_okb (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.
(* mf_words' rows as reader facts over the image reader *)
Lemma img_word_rows : forall i, (i < 5)%nat ->
  exists wp, YG0d.rdword img_rd (wordsA + 8 * Z.of_nat i) = Some wp /\ 0 < wp /\
    SegABase.sa_str img_rd wp (nth i m_file_c.MF_ROLE_WORDS []) /\
    SegABase.sa_romtail Asan.M.loaded_segments (wp + Z.of_nat (length (nth i m_file_c.MF_ROLE_WORDS []))).
Proof.
intros i Hi. apply ptr_str_okb_ok. exact (proj1 (forallb_forall _ _) wordsA_rows i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))).
Qed.
Definition role_row_okb (i : nat) : bool :=
match img_le (rolesA + 4 * Z.of_nat i) 4 with Some v => Z.eqb v (Z.of_nat i) | None => false end.
Lemma rolesA_rows : forallb role_row_okb (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.
(* mf_roles' entries as reader facts over the image reader *)
Lemma img_roles : forall i, (i < 5)%nat -> SegABase.sa_val img_rd (rolesA + 4 * Z.of_nat i) 4 (Z.of_nat i).
Proof.
intros i Hi k Hk.
do 5 (destruct i as [|i]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.
(* the stack-protector cells musl's printf_core, strspn, strstr and strtol read: the GOT word gotwA holds the
   address of __stack_chk_guard, guardA *)
Definition gotwA : Z := 0xa36d8.
Definition guardA : Z := 0x5ff078.
Lemma gotwA_img : img_le gotwA 8 = Some guardA.
Proof. vm_compute. reflexivity. Qed.
(* sa_ssp over the image reader: the GOT word holds guardA, and the guard's word is mapped *)
Lemma img_ssp : SegABase.sa_ssp img_rd gotwA guardA.
Proof. split; [vm_compute; reflexivity | exists 0; vm_compute; reflexivity]. Qed.

(* ===================================== runtime entries ===================================== *)
(* the checked memset / memcpy entries the walks take aintrin_realizes at (__asan_memset, __asan_memcpy) *)
Definition pc_memsetA : Z := seg_sigma SS___asan_memset.
Definition pc_memcpyA : Z := seg_sigma SS___asan_memcpy.
Lemma pc_memsetA_sigma : pc_memsetA = seg_sigma SS___asan_memset. Proof. reflexivity. Qed.
Lemma pc_memcpyA_sigma : pc_memcpyA = seg_sigma SS___asan_memcpy. Proof. reflexivity. Qed.
(* the interceptor trampolines the program calls *)
Definition pc_mallocA : Z := seg_sigma SS___interceptor_trampoline_malloc.
Definition pc_callocA : Z := seg_sigma SS___interceptor_trampoline_calloc.
Definition pc_memchrA : Z := seg_sigma SS___interceptor_trampoline_memchr.
Definition pc_snprintfA : Z := seg_sigma SS___interceptor_trampoline_snprintf.
Definition pc_freeA : Z := seg_sigma SS___interceptor_trampoline_free.
Definition pc_strlenA : Z := seg_sigma SS___interceptor_trampoline_strlen.
Definition pc_strrchrA : Z := seg_sigma SS___interceptor_trampoline_strrchr.
Definition pc_strcmpA : Z := seg_sigma SS___interceptor_trampoline_strcmp.
Definition pc_strchrA : Z := seg_sigma SS___interceptor_trampoline_strchr.
Definition pc_bcmpA : Z := seg_sigma SS___interceptor_trampoline_bcmp.
Definition pc_strncmpA : Z := seg_sigma SS___interceptor_trampoline_strncmp.
Definition pc_strstrA : Z := seg_sigma SS___interceptor_trampoline_strstr.
Definition pc_strspnA : Z := seg_sigma SS___interceptor_trampoline_strspn.
Definition pc_strncasecmpA : Z := seg_sigma SS___interceptor_trampoline_strncasecmp.
Definition pc_strcasecmpA : Z := seg_sigma SS___interceptor_trampoline_strcasecmp.
Definition pc_vsnprintfA : Z := seg_sigma SS___interceptor_trampoline_vsnprintf.
Definition pc_strtolA : Z := seg_sigma SS___interceptor_trampoline_strtol.
Definition pc_strncpyA : Z := seg_sigma SS___interceptor_trampoline_strncpy.
(* musl's word-loop constants (interceptor row 20's MemchrDef.amemchr_realizesM, its memchr_lo / memchr_hi; the
   strlen and strchrnul bodies read the same two words): musl memchr (0x9a2f8) forms them at 0x9a350-0x9a35c,
   `auipc a3,0xfff76; ld a3,24(a3)` (lo + 24, 0x0101010101010100) and `auipc a4,0xfff76; ld a4,-8(a4)` (lo,
   0x8080808080808080); fuzz_command's window is 0x10358 .. 0x10378, the same layout. memchr_code reads those four
   words in the image, memchr_win_img the two constants, memchr_win_rom puts the window in a read-only segment
   (the half of the consts_view fact that needs no allocator record; the unowned / not-errno half is
   the listing's SegRecBase cif_snl_rom field). *)
Definition memchr_loA : Z := 0x10350.
Definition memchr_hiA : Z := 0x10370.
Lemma memchr_code : img_le 0x9a350 4 = Some 0xfff76697 /\ img_le 0x9a354 4 = Some 0x186b683 /\
img_le 0x9a358 4 = Some 0xfff76717 /\ img_le 0x9a35c 4 = Some 0xff873703.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma memchr_win_img : img_le memchr_loA 8 = Some 0x8080808080808080 /\
img_le (memchr_loA + 24) 8 = Some 0x0101010101010100.
Proof. vm_compute. split; reflexivity. Qed.
Definition rom_cover_b (a : Z) : bool :=
existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
  (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) Asan.M.loaded_segments.
Lemma rom_cover_b_ok : forall a, rom_cover_b a = true -> YG0d.in_rom Asan.M.loaded_segments a.
Proof.
intros a H. unfold rom_cover_b in H. apply existsb_exists in H as (sg & Hin & H).
apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
exists sg. split; [exact Hin|]. split; [apply negb_true_iff in H0; exact H0|].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma memchr_win_rom : forall a, memchr_loA <= a < memchr_hiA -> YG0d.in_rom Asan.M.loaded_segments a.
Proof.
intros a Ha. apply rom_cover_b_ok.
assert (H : all_from rom_cover_b memchr_loA (Z.to_nat (memchr_hiA - memchr_loA)) = true)
  by (vm_compute; reflexivity).
apply (all_from_ok _ _ _ H). unfold memchr_loA, memchr_hiA in *. rewrite Z2Nat.id by lia. lia.
Qed.
(* the side-stack entries (classes 0, 1, 3, 5 and the class-5 free) and musl isalnum, called directly *)
Definition pc_stack_malloc_0A : Z := seg_sigma SS___asan_stack_malloc_0.
Definition pc_stack_malloc_1A : Z := seg_sigma SS___asan_stack_malloc_1.
Definition pc_stack_malloc_3A : Z := seg_sigma SS___asan_stack_malloc_3.
Definition pc_stack_malloc_5A : Z := seg_sigma SS___asan_stack_malloc_5.
Definition pc_stack_free_5A : Z := seg_sigma SS___asan_stack_free_5.
Definition pc_isalnumA : Z := seg_sigma SS_isalnum.
(* the shadow fills *)
Definition pc_set_shadow_00A : Z := seg_sigma SS___asan_set_shadow_00.
Definition pc_set_shadow_f5A : Z := seg_sigma SS___asan_set_shadow_f5.
Definition pc_set_shadow_f8A : Z := seg_sigma SS___asan_set_shadow_f8.
(* the entries the interceptor lane's SegRtPC.v names are the listing's *)
Lemma pc_segi :
pc_strcasecmpA = SegRtPC.PC_strcasecmp /\ pc_strncasecmpA = SegRtPC.PC_strncasecmp /\
pc_strstrA = SegRtPC.PC_strstr /\ pc_strchrA = SegRtPC.PC_strchr /\ pc_strrchrA = SegRtPC.PC_strrchr /\
pc_vsnprintfA = SegRtPC.PC_vsnprintf /\ pc_strncpyA = SegRtPC.PC_strncpy /\ pc_callocA = SegRtPC.PC_calloc /\
pc_isalnumA = SegRtPC.PC_isalnum.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the entries and cells the core's lib/A/Rt/RtAPI.v names are the listing's and this file's *)
Lemma pc_rtapi :
pc_strlenA = RtAPI.PC_strlen /\ pc_strcmpA = RtAPI.PC_strcmp /\ pc_strncmpA = RtAPI.PC_strncmp /\
pc_strspnA = RtAPI.PC_strspn /\ pc_memchrA = RtAPI.PC_memchr /\ pc_snprintfA = RtAPI.PC_snprintf /\
pc_strtolA = RtAPI.PC_strtol /\ pc_stack_free_5A = RtAPI.PC_stack_free_5 /\
pc_set_shadow_00A = RtAPI.PC_set_shadow_00 /\ pc_set_shadow_f5A = RtAPI.PC_set_shadow_f5 /\
pc_set_shadow_f8A = RtAPI.PC_set_shadow_f8 /\ gotwA = RtAPI.A_SSP_GOT /\ guardA = RtAPI.A_SSP_GUARD.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ===================================== the stack each call needs ===================================== *)
(* STK_<F>: the bytes below F's entry sp that F and its callees may use: F's own frame, its realignment, and the
   deepest window of a callee called at F's lowest sp. The entry sp is 16-aligned (afn_pre's astk_ok). Runtime
   windows (fuzz_command lib/A/Rt at origin/ossv/recipes 501c0d516c69, the texts the interceptor lane's interface ports):
   strlen ESTACK (RtString.v:80-90), strcmp / strspn 2 * ESTACK (RtString.v:108-154), bcmp 2 * ESTACK (kit
   YG0d.v abcmp_realizes), __asan_stack_malloc_<c> ESTACK (kit YG0d.v astack_malloc_realizes),
   __asan_stack_free_5 ESTACK (RtStack.v:77-92), __asan_set_shadow_<v> ESTACK (RtShadow.v:27-38),
   __asan_memcpy / __asan_memset ESTACK (kit YG0d.v aintrin_realizes, its ecall_pre), the snprintf and vsnprintf
   wrappers 3 * ESTACK (fuzz_command's callers' convention, answer_c.v:56-59 and check_reply_c.v:83-89: 6,672
   bytes measured below the trampoline's entry sp; RtFormat.v:31). INFERENCE: strchr, strncasecmp and
   strcasecmp (interface rows 6, 7, 10, NEW RtSeg texts, not written yet) ask at most 3 * ESTACK. *)
(* trim (0x890a8): frame 32 (0x890a8 `addi sp,sp,-0x20`, released at 0x891b8), no realignment; one call, the
   strlen wrapper (jal 0x89124, ESTACK); the other jal targets are the error arms (errpath_load1 / _store1),
   which do not return. *)
Definition STK_trim : Z := 32 + YG0d.ESTACK.
(* refuse (0x88da4): frame 160 (0x88da4 `addi sp,sp,-0xa0`, released at 0x89058), then 0x88de0
   `andi sp,sp,-0x20` lowers sp by 0 or 16 (sp - 160 is 16-aligned); the variadic spills (0x88e04-0x88e1c, at
   s0 = entry sp - 48 and above) lie inside the frame. Callees at that sp: __asan_stack_malloc_0 (jal 0x88e30,
   ESTACK), the snprintf wrapper (0x88f5c, 0x88f74) and the vsnprintf wrapper (0x88fa4), 3 * ESTACK. The
   real-stack fallback 0x88e4c-0x88e64 (`sub sp,sp,a0` loop) runs only when __asan_stack_malloc_0 returns 0 or the
   use-after-return flag is 0; the kit's astack_malloc_realizes returns the frame and the flag is the record's
   constant 1, so it is dead. *)
Definition STK_refuse : Z := 160 + 16 + 3 * YG0d.ESTACK.
(* cross_check (0x89218): frame 128 (0x89218 `addi sp,sp,-0x80`, released at 0x89494), no realignment; callee
   refuse (jal 0x89350, 0x8939c) at that sp; the other jal targets are error arms. *)
Definition STK_cross_check : Z := 128 + STK_refuse.
(* reac_segconf_parse_file (0x87a78): frame 320 (0x87a78 `addi sp,sp,-0x140`, released at 0x88c60), then 0x87ab8
   `andi sp,sp,-0x20` lowers sp by 0 or 16. Callees at that sp: refuse (11 sites, STK_refuse), trim (5 sites,
   STK_trim), reac_box_catalogue_by_token (0x88538, 64 + 2 * ESTACK, its _c.v), reac_box_catalogue (0x88634, 16,
   its _c.v), the snprintf wrapper (7 sites, 3 * ESTACK), strlen (ESTACK), strcmp / strspn / bcmp (2 * ESTACK),
   strchr / strncasecmp / strcasecmp (at most 3 * ESTACK, INFERENCE above), __asan_stack_malloc_5 (0x87af0),
   __asan_stack_free_5 (0x88c10), __asan_memcpy / __asan_memset, __asan_set_shadow_00 / _f8 (ESTACK each); the
   deepest is refuse's. The class-5 frame (1152 bytes) is on the side stack, not here; the real-stack fallback
   0x87b08-0x87b20 is dead as refuse's. *)
Definition STK_reac_segconf_parse_file : Z := 320 + 16 + Z.max STK_refuse (3 * YG0d.ESTACK).
(* reac_segconf_parse (0x891d0): frame 32 (0x891d0 `addi sp,sp,-0x20`, released at 0x89210), no realignment;
   callees reac_segconf_parse_file (jal 0x891f0) and cross_check (jal 0x891fc) at that sp. *)
Definition STK_reac_segconf_parse : Z := 32 + Z.max STK_reac_segconf_parse_file STK_cross_check.

(* G4 + G5 (the G4 / G5 walk lane's walks; its stack table, read 2026-10-30 16:4xZ: the
   makeup column, each callee window at the sp of its call) *)
(* reac_segconf_init: frame 16 and the checked memset's window (tail call at 0x87a68) *)
Definition STK_reac_segconf_init : Z := 16 + YG0d.ESTACK.
(* check_ignore, check_refusals, check_role: frame 16; no call on the live path (the calls are on dead arms) *)
Definition STK_check_ignore : Z := 16.
Definition STK_check_refusals : Z := 16.
Definition STK_check_role : Z := 16.
(* check_knock_refused: frame 16 and the strstr wrapper (0x8751c, trampoline 0x43a24) *)
Definition STK_check_knock_refused : Z := 16 + 2 * YG0d.ESTACK.
(* check_address: frame 32 and strncmp (0x874e4); strlen (0x874d4) asks ESTACK *)
Definition STK_check_address : Z := 32 + 2 * YG0d.ESTACK.
(* check_segments: frame 48 and strcmp (0x87100) *)
Definition STK_check_segments : Z := 48 + 2 * YG0d.ESTACK.
(* check_model: frame 16 and strcmp (0x87258) *)
Definition STK_check_model : Z := 16 + 2 * YG0d.ESTACK.
(* check_provenance: frame 32 and strcmp (0x8733c, 0x8737c) *)
Definition STK_check_provenance : Z := 32 + 2 * YG0d.ESTACK.
(* check_declared: frame 80 and strcmp (0x876e8) *)
Definition STK_check_declared : Z := 80 + 2 * YG0d.ESTACK.
(* reac_segconf_find: frame 32 and strcmp (0x8954c, in a loop) *)
Definition STK_reac_segconf_find : Z := 32 + 2 * YG0d.ESTACK.
(* the queries over find: their frame and find's window (calls at 0x895ac, 0x89800, 0x896d0, 0x89610) *)
Definition STK_reac_segconf_ignored : Z := 16 + STK_reac_segconf_find.
Definition STK_reac_segconf_model : Z := 16 + STK_reac_segconf_find.
Definition STK_reac_segconf_role_file : Z := 16 + STK_reac_segconf_find.
Definition STK_reac_segconf_role : Z := 32 + STK_reac_segconf_find.
(* name_ok: frame 64 and musl isalnum (0x89dc0, called directly; ESTACK is the upper bound the G4 / G5 walk lane takes
   until the interceptor lane's row 9 names its window) *)
Definition STK_name_ok : Z := 64 + YG0d.ESTACK.
(* reac_declared_vlan_add: frame 112 and strcmp (0x89ef8); memset (0x89f40) and strncpy (0x89f60) ask less *)
Definition STK_reac_declared_vlan_add : Z := 112 + 2 * YG0d.ESTACK.
(* reac_declared_vlan_split: frame 64 and the strtol wrapper with a NULL end pointer (0x89c68, 3 * ESTACK); it
   covers strrchr (0x89be8), strlen (0x89ccc), memcpy (0x89ce8) and name_ok (0x89d08, 64 + STK_name_ok) *)
Definition STK_reac_declared_vlan_split : Z := 64 + 3 * YG0d.ESTACK.
(* reac_segconf_declared: frame 192, the realignment 0x89894 `andi sp,sp,-32` (0 or 16 bytes), and
   reac_declared_vlan_split's window (0x899f8); __asan_stack_malloc_1 (0x898cc) and reac_declared_vlan_add
   (0x89a14) ask less (the G4 / G5 walks confirmed 12,560, 16:55Z) *)
Definition STK_reac_segconf_declared : Z := 192 + 16 + STK_reac_declared_vlan_split.
(* reac_segconf_ignore_file: frame 16 and find's window (0x89768) *)
Definition STK_reac_segconf_ignore_file : Z := 16 + STK_reac_segconf_find.
(* check_absent: frame 32 and the deepest of its four queries (find 0x87600, role 0x87614, ignored 0x87624, model
   0x87634), role's *)
Definition STK_check_absent : Z :=
32 + Z.max (Z.max STK_reac_segconf_find STK_reac_segconf_role) (Z.max STK_reac_segconf_ignored STK_reac_segconf_model).
(* G2 (the G2 walk lane's stk.tsv, 16:46Z; m_file and fuzz_catalogue_row as the contracts lane took them in at m_file's
   intake) *)
(* fuzz_catalogue_row: frame 64 and the kit's abcmp_realizes window (YG0d.v; strlen 0x8a098 asks ESTACK) *)
Definition STK_fuzz_catalogue_row : Z := 64 + 2 * YG0d.ESTACK.
(* reac_box_catalogue: frame 16, no call on the live path *)
Definition STK_reac_box_catalogue : Z := 16.
(* reac_box_catalogue_by_token: its tail jump to fuzz_catalogue_row (0x8a174) runs at the caller's entry sp, so
   fuzz_catalogue_row's window; its own frame 16 and strlen (0x8a15c, ESTACK) ask less *)
Definition STK_reac_box_catalogue_by_token : Z := STK_fuzz_catalogue_row.
(* ieq: frame 48 and strlen (ESTACK) *)
Definition STK_ieq : Z := 48 + YG0d.ESTACK.
(* m_find: frame 48 and bcmp (2 * ESTACK); strlen asks ESTACK *)
Definition STK_m_find : Z := 48 + 2 * YG0d.ESTACK.
(* m_refuse: frame 48 and its two snprintf calls (row 4's asnprintf_realizes window, 2 * ESTACK) *)
Definition STK_m_refuse : Z := 48 + 2 * YG0d.ESTACK.
(* m_file: frame 288, the realignment `andi sp,sp,-32` at 0x85efc (0 or 16 bytes), and the deepest callee window
   at that sp, fuzz_catalogue_row's (0x86878); m_refuse, m_find, its own snprintf (2 * ESTACK), ieq, bcmp and the
   string entries ask less *)
Definition STK_m_file : Z := 288 + 16 + STK_fuzz_catalogue_row.
(* G1 (the G1 walk lane's stk.tsv, 16:32Z): the program interface's window LLVMF_STK (fuzz_command lib/A/ACfn.v:28,
   tfib_lib_pre_x's afn_pre); the harness walk proves its need (320 + 16 + the deepest callee window) is at most
   this *)
Definition STK_LLVMFuzzerTestOneInput : Z := 32768.

(* the values *)
Lemma STK_values :
STK_trim = 4128 /\ STK_refuse = 12464 /\ STK_cross_check = 12592 /\
STK_reac_segconf_parse_file = 12800 /\ STK_reac_segconf_parse = 12832 /\
STK_reac_segconf_init = 4112 /\ STK_check_ignore = 16 /\ STK_check_refusals = 16 /\ STK_check_role = 16 /\
STK_check_knock_refused = 8208 /\ STK_check_address = 8224 /\ STK_check_segments = 8240 /\
STK_check_model = 8208 /\ STK_check_provenance = 8224 /\ STK_check_declared = 8272 /\
STK_reac_segconf_find = 8224 /\ STK_reac_segconf_ignored = 8240 /\ STK_reac_segconf_model = 8240 /\
STK_reac_segconf_role_file = 8240 /\ STK_reac_segconf_role = 8256 /\ STK_name_ok = 4160 /\
STK_reac_declared_vlan_add = 8304 /\ STK_reac_declared_vlan_split = 12352 /\
STK_reac_segconf_declared = 12560 /\ STK_reac_segconf_ignore_file = 8240 /\ STK_check_absent = 8288 /\
STK_fuzz_catalogue_row = 8256 /\ STK_reac_box_catalogue = 16 /\ STK_reac_box_catalogue_by_token = 8256 /\
STK_ieq = 4144 /\ STK_m_find = 8240 /\ STK_m_refuse = 8240 /\ STK_m_file = 8560 /\
STK_LLVMFuzzerTestOneInput = 32768.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ======================================= the literals ======================================= *)
(* equality of two texts, as a boolean *)
Fixpoint zl_eqb (l1 l2 : list Z) : bool :=
match l1, l2 with
| [], [] => true
| a :: r1, b :: r2 => Z.eqb a b && zl_eqb r1 r2
| _, _ => false
end.
Lemma zl_eqb_eq : forall l1 l2 : list Z, zl_eqb l1 l2 = true -> l1 = l2.
Proof.
induction l1 as [|a l1 IH]; intros [|b l2] H; cbn [zl_eqb] in H; try discriminate H; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite H1, (IH l2 H2). reflexivity.
Qed.
Fixpoint lit_find (t : list (list Z * Z)) (s : list Z) : Z :=
match t with
| [] => 0
| (k, a) :: t' => if zl_eqb k s then a else lit_find t' s
end.
(* fuzz_segconf.c's literals, each with the address the code forms (the auipc of the pair at the pc given) *)
Definition SEG_LIT_TAB_FZ : list (list Z * Z) := [
(LLVMFuzzerTestOneInput_c.LIT_LABEL, 0x20fe0);  (* .str    auipc 0x85150 *)
(LLVMFuzzerTestOneInput_c.LIT_PROBE, 0x21020);  (* .str.1  auipc 0x856dc *)
(LLVMFuzzerTestOneInput_c.LIT_NOSUCH, 0x21040); (* .str.2  auipc 0x85780 0x85798 *)
(LLVMFuzzerTestOneInput_c.LIT_ENP, 0x21060);    (* .str.3  auipc 0x85820 0x85854 *)
(TNP, 0x21300);                                 (* .str.22 auipc 0x87514 *)
(F_addr_line, 0x210c0);                         (* .str.6  auipc 0x87850 *)
(F_addr, 0x210e0);                              (* .str.7  auipc 0x87864 *)
(F_s, 0x21080);                                 (* .str.4  auipc 0x86000 0x86924 0x86a24 *)
(S_base, 0x210a0);                              (* .str.5  auipc 0x85ff8 *)
(S_segment, 0x21100);                           (* .str.8  auipc 0x864a0 *)
(S_role, 0x21120);                              (* .str.9  auipc 0x86684 *)
(S_model, 0x21220);                             (* .str.15 auipc 0x867b8 *)
(S_ignore, 0x21240);                            (* .str.16 auipc 0x8693c *)
(S_yes, 0x21260);                               (* .str.17 auipc 0x86954 *)
(S_true, 0x21280);                              (* .str.18 auipc 0x86970 *)
(S_no, 0x212a0);                                (* .str.19 auipc 0x869b0 *)
(S_false, 0x212c0);                             (* .str.20 auipc 0x869c8 *)
(S_knock, 0x212e0)                              (* .str.21 auipc 0x86b20 *)
].
(* reac_segconf.c's literals (the G3 walk lane's table; the pc is that of the pair's addi, the annotated G3 disassembly
   on the unit's internal record at dfb49d6ad789) *)
Definition SEG_LIT_TAB_RC : list (list Z * Z) := [
(F_s, 0x21340);          (* .str    0x87cd8 0x8854c 0x88584 0x8887c 0x888fc 0x88948 0x889e0 *)
(S_base, 0x21360);       (* .str.1  0x87cd0 0x88f3c 0x891e8 *)
([SP; TAB; CR], 0x21380); (* .str.2  0x87dc8 *)
(F_long, 0x213a0);       (* .str.3  0x87dd0 *)
(F_notclosed, 0x21400);  (* .str.4  0x88050 *)
(F_after, 0x21440);      (* .str.5  0x87f9c *)
(S_segment, 0x214a0);    (* .str.6  0x880d0 *)
(F_unknown, 0x214c0);    (* .str.7  0x880e8 *)
(F_noname, 0x21520);     (* .str.8  0x88788 *)
(F_toolong, 0x21560);    (* .str.9  0x88348 *)
(F_bound, 0x215c0);      (* .str.10 0x8881c *)
(F_twice, 0x21620);      (* .str.11 0x8899c *)
(F_neither, 0x216a0);    (* .str.12 0x88098 *)
(F_outside, 0x21700);    (* .str.13 0x881c0 *)
(S_role, 0x21760);       (* .str.14 0x88154 *)
(F_badrole, 0x21780);    (* .str.15 0x884d4 *)
(S_model, 0x21800);      (* .str.16 0x88168 *)
(F_ss, 0x21820);         (* .str.17 0x88694 *)
([124], 0x21840);        (* .str.18 0x88668 *)
([], 0x21860);           (* .str.19 0x88674 *)
(F_badmodel, 0x21880);   (* .str.20 0x886cc *)
(S_ignore, 0x218e0);     (* .str.21 0x8817c *)
(F_badignore, 0x21900);  (* .str.22 0x88418 *)
(S_knock, 0x21960);      (* .str.23 0x88190 *)
(F_knock, 0x21980);      (* .str.24 0x884fc *)
(F_nokey, 0x21a40);      (* .str.25 0x881a4 *)
(S_auto, 0x21ae0);       (* .str.33 0x88454 *)
(S_master, 0x21b00);     (* .str.34 0x8846c *)
(S_slave, 0x21b20);      (* .str.35 0x88484 *)
(S_tap, 0x21b40);        (* .str.36 0x8849c *)
(S_box, 0x21b60);        (* .str.37 0x884b8 *)
(S_yes, 0x21b80);        (* .str.38 0x88368 *)
(S_true, 0x21ba0);       (* .str.39 0x88380 *)
(S_no, 0x21bc0);         (* .str.41 0x883cc *)
(S_false, 0x21be0);      (* .str.42 0x883e0 *)
(F_addr_line, 0x21aa0);  (* .str.31 0x88f4c *)
(F_addr, 0x21ac0);       (* .str.32 0x88f68 *)
(F_xmodel, 0x21c00);     (* .str.44 0x892a0 *)
(F_xbox, 0x21ca0)        (* .str.45 0x892a4 *)
].
(* the contracts' lit at image A, per translation unit *)
Definition seg_litA_fz (s : list Z) : Z := lit_find SEG_LIT_TAB_FZ s.
Definition seg_litA_rc (s : list Z) : Z := lit_find SEG_LIT_TAB_RC s.
(* the texts each map must cover: the harness contract's two lists *)
Definition FZ_LITS : list (list Z) := LLVMFuzzerTestOneInput_c.LTOI_FZ_LITS.
Definition RC_LITS : list (list Z) := LLVMFuzzerTestOneInput_c.LTOI_RC_LITS.
(* x's address under the map is positive, an object of the listing, holds x and its NUL in the image, has its
   ROM tail, and the literal ends below longl *)
Definition lit_okb (tab : list (list Z * Z)) (x : list Z) : bool :=
(0 <? lit_find tab x) && existsb (Z.eqb (lit_find tab x)) seg_objs &&
img_bytes_b (lit_find tab x) (x ++ [0]) && romtail_b (lit_find tab x + Z.of_nat (length x)) &&
(lit_find tab x + Z.of_nat (length x) + 1 <=? longlA).
Definition lit_facts (lit : list Z -> Z) (x : list Z) : Prop :=
0 < lit x /\ In (lit x) seg_objs /\
(forall i, (i < length (x ++ [0%Z]))%nat -> img_rd (lit x + Z.of_nat i) = Some (nth i (x ++ [0%Z]) 0%Z)) /\
SegABase.sa_romtail Asan.M.loaded_segments (lit x + Z.of_nat (length x)) /\
lit x + Z.of_nat (length x) + 1 <= longlA.
Lemma lit_okb_facts : forall tab x, lit_okb tab x = true -> lit_facts (lit_find tab) x.
Proof.
intros tab x H. unfold lit_okb in H. unfold lit_facts.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H1 H2].
split; [apply Z.ltb_lt; exact H1|].
split; [apply existsb_exists in H2 as (a & Ha & E); apply Z.eqb_eq in E; rewrite E; exact Ha|].
split; [exact (img_bytes_b_ok _ _ H3)|].
split; [exact (romtail_b_ok _ H4) | apply Z.leb_le; exact H5].
Qed.
Lemma seg_litA_fz_okb : forallb (lit_okb SEG_LIT_TAB_FZ) FZ_LITS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_litA_rc_okb : forallb (lit_okb SEG_LIT_TAB_RC) RC_LITS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_litA_fz_facts : forall s, In s FZ_LITS -> lit_facts seg_litA_fz s.
Proof. intros s Hs. exact (lit_okb_facts _ _ (proj1 (forallb_forall _ _) seg_litA_fz_okb s Hs)). Qed.
Lemma seg_litA_rc_facts : forall s, In s RC_LITS -> lit_facts seg_litA_rc s.
Proof. intros s Hs. exact (lit_okb_facts _ _ (proj1 (forallb_forall _ _) seg_litA_rc_okb s Hs)). Qed.
Lemma seg_litA_fz_pos : forall s, In s FZ_LITS -> 0 < seg_litA_fz s.
Proof. intros s Hs. exact (proj1 (seg_litA_fz_facts s Hs)). Qed.
Lemma seg_litA_rc_pos : forall s, In s RC_LITS -> 0 < seg_litA_rc s.
Proof. intros s Hs. exact (proj1 (seg_litA_rc_facts s Hs)). Qed.
Lemma seg_litA_fz_romtail : forall s, In s FZ_LITS ->
SegABase.sa_romtail Asan.M.loaded_segments (seg_litA_fz s + Z.of_nat (length s)).
Proof. intros s Hs. exact (proj1 (proj2 (proj2 (proj2 (seg_litA_fz_facts s Hs))))). Qed.
Lemma seg_litA_rc_romtail : forall s, In s RC_LITS ->
SegABase.sa_romtail Asan.M.loaded_segments (seg_litA_rc s + Z.of_nat (length s)).
Proof. intros s Hs. exact (proj1 (proj2 (proj2 (proj2 (seg_litA_rc_facts s Hs))))). Qed.
(* no literal of either list holds a NUL, so each is a C string of the image reader at its address *)
Lemma lits_nonul : forallb (fun s => negb (existsb (Z.eqb 0) s)) (FZ_LITS ++ RC_LITS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_litA_fz_str : forall s, In s FZ_LITS -> SegABase.sa_str img_rd (seg_litA_fz s) s.
Proof.
intros s Hs. destruct (seg_litA_fz_facts s Hs) as (_ & _ & HB & HT & _).
assert (H0 : negb (existsb (Z.eqb 0) s) = true)
  by exact (proj1 (forallb_forall _ _) lits_nonul s (in_or_app _ _ _ (or_introl Hs))).
split; [split; [exact HB | exact (nonul_ok _ H0)] | exact (romtail_img_tail _ HT)].
Qed.
Lemma seg_litA_rc_str : forall s, In s RC_LITS -> SegABase.sa_str img_rd (seg_litA_rc s) s.
Proof.
intros s Hs. destruct (seg_litA_rc_facts s Hs) as (_ & _ & HB & HT & _).
assert (H0 : negb (existsb (Z.eqb 0) s) = true)
  by exact (proj1 (forallb_forall _ _) lits_nonul s (in_or_app _ _ _ (or_intror Hs))).
split; [split; [exact HB | exact (nonul_ok _ H0)] | exact (romtail_img_tail _ HT)].
Qed.
(* each callee's list is inside its module's list *)
Lemma lits_incl :
incl check_knock_refused_c.check_knock_refused_LITS FZ_LITS /\ incl m_refuse_c.M_REFUSE_LITS FZ_LITS /\
incl m_file_c.M_FILE_LITS FZ_LITS /\ incl LLVMFuzzerTestOneInput_c.LTOI_LITS FZ_LITS /\
incl reac_segconf_parse_file_c.PARSE_FILE_LITS RC_LITS /\ incl cross_check_c.CROSS_CHECK_LITS RC_LITS /\
incl refuse_c.REFUSE_LITS RC_LITS.
Proof.
unfold FZ_LITS, RC_LITS, LLVMFuzzerTestOneInput_c.LTOI_FZ_LITS, LLVMFuzzerTestOneInput_c.LTOI_RC_LITS.
split; [intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx|].
split; [intros x Hx; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hx|].
split; [intros x Hx; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hx|].
split; [intros x Hx; apply in_or_app; left; exact Hx|].
split; [intros x Hx; apply in_or_app; left; exact Hx|].
split; [intros x Hx; apply in_or_app; right; exact Hx|].
intros x Hx. apply in_or_app. right. unfold cross_check_c.CROSS_CHECK_LITS. apply in_or_app. right. exact Hx.
Qed.
Lemma seg_litA_rc_S_base : seg_litA_rc S_base = 0x21360.
Proof. vm_compute. reflexivity. Qed.
(* the (address, size with the NUL) of every entry of both maps: the join with the listing's
   SegRecBase.seg_lit_objs, over which seg_lit_pinned gives each literal's shadow at every allocator state *)
Definition SEG_LIT_OBJS_A : list (Z * Z) :=
map (fun e => (snd e, Z.of_nat (length (fst e)) + 1)) (SEG_LIT_TAB_FZ ++ SEG_LIT_TAB_RC).
