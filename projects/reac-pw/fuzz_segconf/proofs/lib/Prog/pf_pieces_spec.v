(** reac-pw/fuzz_segconf: the build-independent part of the piece contracts of reac_segconf_parse_file (family F3).
    Both lib/Prog/reac_segconf_parse_file_pieces_c.v (plain, image 3776ca44d75c) and
    lib/U/Prog/reac_segconf_parse_file_pieces_c.v (UBSan, image 1696d6c34ffd) Require this file. It holds the record of
    the frame's saved registers, the line loop's account in the spine's terms (lib/Spec/SegModel.v), the provenance
    edit of the role / ignore / model branches, the .rodata addresses the cuts name, and the small lemmas the pieces
    need, each stated as a Prop. Statement text only: no lemma is proved here, and no function of the binary.

    Sources: the binary's reac_segconf_parse_file (what it inlines, its frame, its call sites, its loops, the pieces
    and the invariants); notes O1 and O2 below. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** The frame's saved registers
    The entry values of ra and s0-s11. The prologue stores them at 13 consecutive 8-byte slots, s11 lowest and ra
    highest (plain sp + 0x368 .. 0x3c8, UBSan sp + 0x3b8 .. 0x418), and the epilogue loads them
    back: the function's post gives them back unchanged. *)
Record pf_sv := PFSv {
  sv_ra : word; sv_s0 : word; sv_s1 : word; sv_s2 : word; sv_s3 : word; sv_s4 : word; sv_s5 : word;
  sv_s6 : word; sv_s7 : word; sv_s8 : word; sv_s9 : word; sv_s10 : word; sv_s11 : word }.
(** The words at the slots, lowest first (seg_spec.saved_at's list: the prologue's order). *)
Definition sv_list (v : pf_sv) : list word :=
  [sv_s11 v; sv_s10 v; sv_s9 v; sv_s8 v; sv_s7 v; sv_s6 v; sv_s5 v; sv_s4 v; sv_s3 v; sv_s2 v; sv_s1 v; sv_s0 v;
   sv_ra v].

(** ** .rodata addresses the cuts name (the same in both images) *)
Definition PF_STR_S : Z := 0x104e0.           (* "%s" *)
Definition PF_STR_BLANKS : Z := 0x10954.      (* " \t\r", R:144's strspn set *)
Definition PF_STR_LONG : Z := 0x10628.        (* SegModel.F_long *)
Definition PF_STR_NOTCLOSED : Z := 0x10397.   (* F_notclosed *)
Definition PF_STR_AFTER : Z := 0x10657.       (* F_after *)
Definition PF_STR_UNKNOWN : Z := 0x108f7.     (* F_unknown *)
Definition PF_STR_NEITHER : Z := 0x10884.     (* F_neither *)
Definition PF_STR_OUTSIDE : Z := 0x10402.     (* F_outside *)
Definition PF_STR_BADROLE : Z := 0x10958.     (* F_badrole *)
Definition PF_STR_BADIGNORE : Z := 0x10714.   (* F_badignore *)
Definition PF_STR_KNOCK : Z := 0x10762.       (* F_knock *)
Definition PF_STR_NOKEY : Z := 0x10680.       (* F_nokey *)
(** "tap\0" and "box\0" read as little-endian words: the two frame slots the role branch compares low[0..3] with
    (plain sp + 0x18 / 0x10, UBSan sp + 0x28 / 0x20; reac_role.h:117-118). *)
Definition PF_TAP_WORD : Z := 0x00706174.
Definition PF_BOX_WORD : Z := 0x00786f62.

(** ** The line loop's account (R:131-136)
    The text s (no NUL; its NUL follows it in memory). A line starts at offset o: [pf_line s o] is its bytes (up to
    the next '\n', or the rest of the text), [pf_next s o] the offset of the next line (past the '\n', or the end),
    [pf_tline s o] the line the header and key branches see (copied into buf, comment cut, trimmed: R:151-155). *)
Definition pf_line (s : list Z) (o : nat) : list Z := fst (break_nl (skipn o s)).
Definition pf_next (s : list Z) (o : nat) : nat := (length s - length (snd (break_nl (skipn o s))))%nat.
Definition pf_tline (s : list Z) (o : nat) : list Z := r_trim (r_strip_comment (pf_line s o)).

(** At a line start o: the lines d before it have been read (lineno ln = length d, the number of lines consumed), and
    each of them took at least one byte (so ln <= o <= 65535, which discharges UBSan's `lineno++` check at 0x153ec). *)
Definition pf_lctx (s : list Z) (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  (o <= length s)%nat /\ lines s = d ++ lines (skipn o s) /\ ln = Z.of_nat (length d) /\ ln <= Z.of_nat o.

(** The spine's state before the loop (R:122-123, r_parse_file's c1: reading from the label, gen + 1) and after the
    lines d: at every pass the loop head's (rc, cur, cur_name) is pf_spine rc0 lab d for the entry state rc0, the
    label lab and the lines d consumed (P1 starts it with d = [], each pass applies r_line: L_r_lines_app). The cuts
    are stated for every state (rc, cur, nm), which is the stronger statement; this is the instance the loop meets. *)
Definition pf_start (rc0 : rconf) (lab : option (list Z)) : rconf :=
  RConf (rc_seg rc0) (rc_refusal rc0) (rc_refused rc0) (rc_overflow rc0)
        (snprintf_s 96 F_s [AS (match lab with Some l => l | None => S_base end)]) (rc_gen rc0 + 1).
Definition pf_spine (rc0 : rconf) (lab : option (list Z)) (d : list (list Z)) : rconf * option nat * list Z :=
  r_lines (pf_start rc0 lab, None, []) 0 d.

(** The room of the u32 counters c->refused and c->overflow while k text bytes are left: every line adds at most
    one refusal and one overflow and takes at least one byte. reader_pre gives rc_refused rc + 2^17 < 2^32 and the
    same for overflow, and the text has at most 65535 < 2^16 bytes, so this holds at the loop head; every refuse call
    then has refuse_pre's rc_refused rc + 1 < 2^32. *)
Definition pf_cnt (rc : rconf) (k : nat) : Prop :=
  rc_refused rc + Z.of_nat k + 2 ^ 16 < 2 ^ 32 /\ rc_overflow rc + Z.of_nat k + 2 ^ 16 < 2 ^ 32.

(** cur (R:126) in the spine's terms: None is NULL, Some i is &c->seg[i] = c + 356 i, an entry the table holds. *)
Definition pf_cur_ptr (c : Z) (cur : option nat) : Z := match cur with None => 0 | Some i => rseg_addr c i end.
Definition pf_cur_ok (rc : rconf) (cur : option nat) : Prop :=
  match cur with None => True | Some i => (i < length (rc_seg rc))%nat end.

(** The C string l at a and its NUL lie in parse_file's buf[512], which starts at b (b = sp + the build's offset). *)
Definition pf_inb (b a : Z) (l : list Z) : Prop := b <= a /\ a + Z.of_nat (length l) < b + 512.

(** ** The provenance edit (R:244-246, R:268-270, R:278-280)
    The role, ignore and model branches first store the value fields of cur, then snprintf(field_file, 96, "%s",
    c->reading) at one shared site. Between the two, c holds [pf_prov_mid]: the value fields set, the file field
    still the old one; after the snprintf it holds [pf_prov_fin], which is the spine's r_upd of r_key. *)
Inductive pf_prov := PRole (r : Z) | PIgn (b : bool) | PModel (mdl : list Z).
Definition pf_prov_off (k : pf_prov) : Z :=
  match k with PRole _ => RS_ROLE_FILE | PIgn _ => RS_IGNORE_FILE | PModel _ => RS_MODEL_FILE end.
Definition pf_prov_set (k : pf_prov) (file : list Z) (g : rseg) : rseg :=
  match k with
  | PRole r => rs_with_role r file g
  | PIgn b => rs_with_ignore b file g
  | PModel mdl => rs_with_model mdl file g
  end.
Definition pf_prov_old (k : pf_prov) (g : rseg) : list Z :=
  match k with PRole _ => rs_role_file g | PIgn _ => rs_ignore_file g | PModel _ => rs_model_file g end.
Definition pf_prov_mid (k : pf_prov) (rc : rconf) (gi : nat) : rconf :=
  r_upd rc gi (fun g => pf_prov_set k (pf_prov_old k g) g).
Definition pf_prov_fin (k : pf_prov) (rc : rconf) (gi : nat) : rconf :=
  r_upd rc gi (pf_prov_set k (snprintf_s 96 F_s [AS (rc_reading rc)])).

(** ** The role step at reac_role_intent_parse (R:236-246, RR:110-120)
    Once low holds r_low val 0 64 and its NUL, the line's step is the spine's r_key role branch, stated against
    SegModel.role_intent_parse (strcmp-based; the binary's bcmp / word compares agree with it by O1 below). *)
Definition pf_role_step (rc : rconf) (gi : nat) (nm : list Z) (ln : Z) (val : list Z) : rconf * option nat * list Z :=
  match role_intent_parse (r_low val 0 64) with
  | None => (refuse rc ln F_badrole [AS nm; AS val], Some gi, nm)
  | Some r => (r_upd rc gi (rs_with_role r (snprintf_s 96 F_s [AS (rc_reading rc)])), Some gi, nm)
  end.

(** The value the role branch builds from low[0..3] with `lbu, lbu, lbu, lb` (bytes 0-2 unsigned, byte 3
    sign-extended, then shifted and or-ed: plain 0x1522c .. 0x15250, UBSan 0x1587c .. 0x158a0) and compares as a
    64-bit word with the tap / box slot: the register holds Z_to_bv 64 (pf_word4 B). *)
Definition pf_word4 (B : list byte) : Z :=
  let b := fun i => bv_unsigned (nth i B ZERO) in
  b 0%nat + 256 * b 1%nat + 65536 * b 2%nat + 16777216 * (if b 3%nat <? 128 then b 3%nat else b 3%nat - 256).

(** ** The lemmas the pieces need (statements only) *)

(** O1, the bcmp half: reac_role_intent_parse's strcmp(low, "auto" / "master" / "slave")
    compiles to bcmp(low, lit, 5 / 7 / 6) (plain 0x151f4 / 0x1520c / 0x15224, UBSan 0x15844 / 0x1585c / 0x15874),
    5 / 7 / 6 = S (length w) for w = S_auto / S_master / S_slave. It reads that many bytes of the 64-byte buffer B,
    past low's NUL into bytes an earlier line left there. Its result (bcmp_c.v: memcmp_model of the bytes) is 0
    exactly when the C string l at B equals w, because the literal's NUL is among the compared bytes. *)
Definition O1_bcmp_lit : Prop :=
  forall (B : list byte) (l w : list Z) (v : Z),
    ~ In 0 l -> ~ In 0 w -> Forall (fun x => 0 <= x < 256) w ->
    firstn (S (length l)) (zs B) = l ++ [0] ->
    memcmp_model B (zb (w ++ [0])) (S (length w)) = Some v ->
    (v = 0 <-> strcmp l w = 0).

(** O1, the word half: strcmp(low, "tap" / "box") compiles to one compare of pf_word4 B with the "tap\0" / "box\0"
    word; it is equal exactly when the C string l at B is "tap" / "box". *)
Definition O1_word_lit : Prop :=
  forall (B : list byte) (l : list Z),
    ~ In 0 l -> (4 <= length B)%nat -> firstn (S (length l)) (zs B) = l ++ [0] ->
    (pf_word4 B = PF_TAP_WORD <-> strcmp l S_tap = 0) /\ (pf_word4 B = PF_BOX_WORD <-> strcmp l S_box = 0).

(** O2: the long-line branch calls strspn(at, " \t\r") on the REST of the text from the line's
    start (plain 0x14e10, UBSan 0x15400), while SegModel.r_line applies strspn_blank to the line only. The byte after
    the line is '\n' or the text's end (its NUL), neither of them a blank, so the scan stops there and the two
    agree. (Prog/strspn_c.v returns spn_len set str for the C string str at a0; with set = the bytes of " \t\r"
    that is strspn_blank (zs str): the walk's local fact about the two list functions.) *)
Definition O2_strspn_rest : Prop :=
  forall rest : list Z, ~ In 0 rest ->
    (nth (length (fst (break_nl rest))) rest 0 = NL \/ length (fst (break_nl rest)) = length rest) /\
    strspn_blank rest = strspn_blank (fst (break_nl rest)).

(** One pass of the loop reads one line: lines (R:131-136's split) of a non-empty rest is its first line, then
    the lines of what follows. *)
Definition L_lines_step : Prop :=
  forall p : list Z, p <> [] -> lines p = fst (break_nl p) :: lines (snd (break_nl p)).

(** strchr(p, '\n') and strlen(p) (R:132-133) on the rest p of the text: the '\n' ends the line, or the line is
    the whole rest. *)
Definition L_break_nl : Prop :=
  forall p : list Z, ~ In 0 p ->
    (strchr p NL = Some (length (fst (break_nl p))) /\ p = fst (break_nl p) ++ NL :: snd (break_nl p)) \/
    (strchr p NL = None /\ fst (break_nl p) = p /\ snd (break_nl p) = []).

(** The next line's offset (R:135: nl + 1, or p + len) and the rest there. *)
Definition L_next : Prop :=
  forall (s : list Z) (o : nat), (o < length s)%nat ->
    skipn (pf_next s o) s = snd (break_nl (skipn o s)) /\ (o < pf_next s o)%nat /\ (pf_next s o <= length s)%nat /\
    pf_next s o = (o + length (pf_line s o) + (if (o + length (pf_line s o) <? length s)%nat then 1 else 0))%nat.

(** buf[0 .. len) = the line's bytes (the memcpy of R:151 copies the bytes [o, o + len) of the text), with no NUL
    and no '\n' in them; R:152 then stores buf[len] = 0. *)
Definition L_line_bytes : Prop :=
  forall (s : list Z) (o : nat), ~ In 0 s ->
    pf_line s o = firstn (length (pf_line s o)) (skipn o s) /\ ~ In 0 (pf_line s o) /\ ~ In NL (pf_line s o).

(** strip_comment's result in buf (R:65-74, inlined: the loop at plain 0x14e68 / UBSan 0x15474): the NUL goes to
    the first comment start k, or nothing is cut. *)
Definition L_strip : Prop :=
  forall l : list Z, ~ In 0 l ->
    exists k : nat, (k <= length l)%nat /\ r_strip_comment l = firstn k l /\
      (forall j, (j < k)%nat -> r_comment_at l j = false) /\ ((k < length l)%nat -> r_comment_at l k = true).

(** trim's result in buf (trim_c.v: a0 = p + trim_lead s, the NUL at trim_lead s + length (r_trim s)): the trimmed
    string is the bytes of l from trim_lead l on. *)
Definition L_trim : Prop :=
  forall l : list Z, ~ In 0 l ->
    (trim_lead l + length (r_trim l) <= length l)%nat /\
    r_trim l = firstn (length (r_trim l)) (skipn (trim_lead l) l) /\ ~ In 0 (r_trim l).

(** The fold buffers (R:236-238 into low[64], R:254-256 into low[24]): the bytes stored before the NUL are the
    harness's fold of the C string, cut at cap - 1. *)
Definition L_low : Prop :=
  forall (v : list Z) (cap : nat), r_low v 0 cap = h_fold (cut_nul v) cap /\ ~ In 0 (r_low v 0 cap).

(** The known join (R:258-263, the loop at plain 0x15330 / UBSan 0x159b4): after ti of the 11 tokens, known[0 ..
    kn] holds their join J and its NUL, kn = length J <= 77 (seg_spec.known_length), and the rest of the loop gives
    SegModel.known. *)
Definition L_known : Prop :=
  forall ti : nat, (ti <= 11)%nat ->
    let J := known_go (firstn ti cat_toks) true 0 [] in
    (length J <= 77)%nat /\ ~ In 0 J /\
    known_go (skipn ti cat_toks) (Nat.eqb ti 0) (Z.of_nat (length J)) J = known.

(** The rest of the text at p = t + o is a C string with the text's slack (what strchr / strlen / strspn read). *)
Definition L_cstr_skipn : Prop :=
  forall (segs : list Segment) (m : word -> option byte) (t : Z) (s : list Z) (o : nat),
    cstr_at segs m t s -> (o <= length s)%nat -> cstr_at segs m (t + Z.of_nat o) (skipn o s).

(** The lines read so far and the lines left: one pass appends one line to d (pf_spine rc0 lab (d ++ [l]) is
    r_line applied to pf_spine rc0 lab d, with the line number length d + 1). *)
Definition L_r_lines_app : Prop :=
  forall (st : rconf * option nat * list Z) (n : Z) (d e : list (list Z)),
    r_lines st n (d ++ e) = r_lines (r_lines st n d) (n + Z.of_nat (length d)) e.

(** r_parse_file is the loop from pf_start (what P1 sets up before the head) and c->n of its final state. *)
Definition L_parse_start : Prop :=
  forall (rc0 : rconf) (s : list Z) (lab : option (list Z)),
    r_parse_file rc0 s lab =
      (fst (fst (r_lines (pf_start rc0 lab, None, []) 0 (lines s))),
       Z.of_nat (length (rc_seg (fst (fst (r_lines (pf_start rc0 lab, None, []) 0 (lines s))))))).
