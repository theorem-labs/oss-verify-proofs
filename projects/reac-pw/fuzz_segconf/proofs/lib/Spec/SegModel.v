(** * SegModel: the semantic spine of reac-pw/fuzz_segconf (statement text and Gallina proofs; no machine walk).

    Sources (ossv/recipes 25e3d17bdb50, projects/reac-pw/fuzz_segconf/): source/fuzz_segconf.c (the harness, "H:"
    below), source/fuzz.h ("F:"), source/catalogue.c ("K:"); the reader of the pinned build's tree
    (pau-pipeline-next3/reac-pw/result/image/src/): reac-pw/src/reac_segconf.c ("R:"), reac-pw/src/reac_declared_vlan.c
    ("V:"), libreac/include/reac/reac_role.h ("RR:"); musl for the libc leaves. Pinned ELFs: plain 3776ca44d75c, ubsan
    1696d6c34ffd (the 17 refusal formats of R: below are byte-equal in both, checked 2026-10-30).

    Shape (as reac-pw/fuzz_role's spine): one Gallina model per C implementation, each mirroring its C text closely
    so that a machine walk can prove "this binary function computes this Gallina function", then lemmas relating
    the two models, then the agreement theorem: on every payload every check_* of the harness passes.

    Bytes are values in Z (C char is unsigned on riscv64). A [list Z] that stands for a C string holds the bytes
    before its NUL; the decode below only ever builds NUL-free texts. *)
From Stdlib Require Import String Ascii.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

(** ** 0. Bytes, texts, list helpers *)

Definition sb (s : string) : list Z :=
  map (fun a => Z.of_nat (nat_of_ascii a)) (list_ascii_of_string s).

Notation TAB := 9 (only parsing).
Notation NL := 10 (only parsing).
Notation CR := 13 (only parsing).
Notation SP := 32 (only parsing).
Notation DQ := 34 (only parsing).
Notation HASH := 35 (only parsing).
Notation PCT := 37 (only parsing).
Notation SQ := 39 (only parsing).
Notation DOT := 46 (only parsing).
Notation SEMI := 59 (only parsing).
Notation EQ := 61 (only parsing).
Notation LBR := 91 (only parsing).
Notation RBR := 93 (only parsing).

Fixpoint cut_nul (l : list Z) : list Z :=
  match l with [] => [] | b :: r => if b =? 0 then [] else b :: cut_nul r end.
Definition nulfree (l : list Z) : Prop := ~ In 0 l.
Definition hd0 (l : list Z) : Z := match l with [] => 0 | b :: _ => b end.
(** [slice i j l] = the bytes [i, j) of l. *)
Definition slice (i j : nat) (l : list Z) : list Z := firstn (j - i) (skipn i l).

Fixpoint leqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && leqb a' b'
  | _, _ => false
  end.
Fixpoint prefixb (p l : list Z) : bool :=
  match p, l with
  | [], _ => true
  | x :: p', y :: l' => (x =? y) && prefixb p' l'
  | _ :: _, [] => false
  end.
Fixpoint infixb (n h : list Z) : bool :=
  prefixb n h || match h with [] => false | _ :: r => infixb n r end.
Fixpoint dropwhile (P : Z -> bool) (l : list Z) : list Z :=
  match l with [] => [] | b :: r => if P b then dropwhile P r else l end.
Fixpoint takewhile (P : Z -> bool) (l : list Z) : list Z :=
  match l with [] => [] | b :: r => if P b then b :: takewhile P r else [] end.

(** Character classes. [blank] is H:113-116 and the set of R:52,55 and R:144's strspn. *)
Definition blank (c : Z) : bool := (c =? SP) || (c =? TAB) || (c =? CR).
Definition sp_tab (c : Z) : bool := (c =? SP) || (c =? TAB).
Definition is_mark (c : Z) : bool := (c =? HASH) || (c =? SEMI).
(** The ASCII fold H:133,145 and R:237,255 write inline. *)
Definition lower (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c - 65 + 97 else c.

(** ** 1. libc leaves (musl), over C strings *)

(** tolower: [isupper(c) ? c | 32 : c], isupper = [(unsigned)c - 'A' < 26]. *)
Definition tolower (c : Z) : Z := if (65 <=? c) && (c <=? 90) then Z.lor c 32 else c.
(** isdigit [(unsigned)c - '0' < 10]; isalpha [((unsigned)c | 32) - 'a' < 26]; isalnum = isalpha || isdigit. Their
    argument is a byte, [(unsigned char)*p] (V:25, V:43); [isalpha] is stated on that domain [0, 256). *)
Definition isdigit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition isalpha (c : Z) : bool :=
  (0 <=? c) && (c <? 256) && (97 <=? Z.lor c 32) && (Z.lor c 32 <=? 122).
Definition isalnum (c : Z) : bool := isalpha c || isdigit c.

(** strlen. *)
Definition strlen (s : list Z) : nat := length (cut_nul s).
(** strchr(s, c), c <> 0: the index of the first c before the NUL. *)
Fixpoint strchr (s : list Z) (c : Z) : option nat :=
  match s with
  | [] => None
  | b :: r => if b =? c then Some 0%nat else if b =? 0 then None else option_map S (strchr r c)
  end.
(** memchr(s, c, length s): the index of the first c in the whole buffer. *)
Fixpoint memchr (s : list Z) (c : Z) : option nat :=
  match s with
  | [] => None
  | b :: r => if b =? c then Some 0%nat else option_map S (memchr r c)
  end.
(** strrchr(s, c), c <> 0: the index of the last c before the NUL. *)
Fixpoint last_idx (c : Z) (l : list Z) (i : nat) (acc : option nat) : option nat :=
  match l with [] => acc | b :: r => last_idx c r (S i) (if b =? c then Some i else acc) end.
Definition strrchr (s : list Z) (c : Z) : option nat := last_idx c (cut_nul s) 0 None.
(** strspn(s, " \t\r"). *)
Definition strspn_blank (s : list Z) : nat := length (takewhile blank (cut_nul s)).
(** strcmp: [for (; *l == *r && *l; l++, r++); return *l - *r;] (the end of a list reads as its NUL). *)
Fixpoint strcmp (l r : list Z) : Z :=
  match l, r with
  | a :: l', b :: r' => if (a =? b) && negb (a =? 0) then strcmp l' r' else a - b
  | a :: _, [] => a
  | [], b :: _ => - b
  | [], [] => 0
  end.
(** strcasecmp: [for (; *l && *r && ( *l == *r || tolower( *l) == tolower( *r)); l++, r++);
    return tolower( *l) - tolower( *r);] *)
Fixpoint strcasecmp (l r : list Z) : Z :=
  match l, r with
  | a :: l', b :: r' =>
      if negb (a =? 0) && negb (b =? 0) && ((a =? b) || (tolower a =? tolower b)) then strcasecmp l' r'
      else tolower a - tolower b
  | _, _ => tolower (hd0 l) - tolower (hd0 r)
  end.
(** strncasecmp: [if (!n--) return 0; for (; *l && *r && n && (...); l++, r++, n--); return tolower( *l) - tolower( *r);] *)
Fixpoint strncasecmp_go (l r : list Z) (n : nat) : Z :=
  match n with
  | O => tolower (hd0 l) - tolower (hd0 r)
  | S n' =>
      match l, r with
      | a :: l', b :: r' =>
          if negb (a =? 0) && negb (b =? 0) && ((a =? b) || (tolower a =? tolower b)) then strncasecmp_go l' r' n'
          else tolower a - tolower b
      | _, _ => tolower (hd0 l) - tolower (hd0 r)
      end
  end.
Definition strncasecmp (l r : list Z) (n : nat) : Z :=
  match n with O => 0 | S n' => strncasecmp_go l r n' end.
(** strncmp: [if (!n--) return 0; for (; *l && *r && n && *l == *r; l++, r++, n--); return *l - *r;] *)
Fixpoint strncmp_go (l r : list Z) (n : nat) : Z :=
  match n with
  | O => hd0 l - hd0 r
  | S n' =>
      match l, r with
      | a :: l', b :: r' => if negb (a =? 0) && negb (b =? 0) && (a =? b) then strncmp_go l' r' n' else a - b
      | _, _ => hd0 l - hd0 r
      end
  end.
Definition strncmp (l r : list Z) (n : nat) : Z := match n with O => 0 | S n' => strncmp_go l r n' end.
(** strstr(hay, needle) <> NULL: needle occurs in the C string hay. (musl's two-way search; its contract is this.) *)
Definition strstr_found (hay needle : list Z) : bool := infixb needle (cut_nul hay).
(** strtol(s, NULL, 10) on a string of decimal digits only (V:42-45 calls it only there); the value is exact below
    2^63, which every call here meets (a segment name has at most 15 bytes). *)
Definition strtol10 (s : list Z) : Z := fold_left (fun v d => v * 10 + (d - 48)) s 0.

(** ** 2. printf, abstract but exact for every conversion the two texts use: %s, %d, %u, %zu, %.NNs *)

Inductive arg := AS (s : list Z) | AI (z : Z).
Definition arg_s (a : arg) : list Z := match a with AS s => cut_nul s | AI _ => [] end.
Definition arg_i (a : arg) : Z := match a with AI z => z | AS _ => 0 end.

Fixpoint dec_go (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => let acc' := (48 + n mod 10) :: acc in if n <? 10 then acc' else dec_go f (n / 10) acc'
  end.
(** The decimal text of an integer of fewer than 21 digits (int, unsigned, size_t). *)
Definition dec (z : Z) : list Z := if z <? 0 then 45 :: dec_go 20 (- z) [] else dec_go 20 z [].

Fixpoint fmt (f : list Z) (a : list arg) : list Z :=
  match f with
  | [] => []
  | c :: f1 =>
      if negb (c =? PCT) then c :: fmt f1 a else
      match f1 with
      | [] => []
      | c1 :: f2 =>
          if c1 =? 115 then match a with x :: a' => arg_s x ++ fmt f2 a' | [] => [] end
          else if (c1 =? 100) || (c1 =? 117) then match a with x :: a' => dec (arg_i x) ++ fmt f2 a' | [] => [] end
          else if c1 =? 122 then
            match f2 with
            | c2 :: f3 => if c2 =? 117 then match a with x :: a' => dec (arg_i x) ++ fmt f3 a' | [] => [] end else []
            | [] => []
            end
          else if c1 =? 46 then
            match f2 with
            | d1 :: d2 :: c3 :: f4 =>
                if isdigit d1 && isdigit d2 && (c3 =? 115) then
                  match a with
                  | x :: a' => firstn (Z.to_nat ((d1 - 48) * 10 + (d2 - 48))) (arg_s x) ++ fmt f4 a'
                  | [] => []
                  end
                else []
            | _ => []
            end
          else []
      end
  end.

(** snprintf(dst, n, f, a), n >= 1: the C string it stores, and its return value. *)
Definition snprintf_s (n : Z) (f : list Z) (a : list arg) : list Z := firstn (Z.to_nat (n - 1)) (fmt f a).
Definition snprintf_r (f : list Z) (a : list arg) : Z := Z.of_nat (length (fmt f a)).

(** The texts. *)
Definition EMDASH : list Z := [226; 128; 148].
Local Open Scope string_scope.
Definition F_s := sb "%s".
Definition F_ss := sb "%s%s".
Definition F_addr_line := sb "%s:%d: ".
Definition F_addr := sb "%s: ".
Definition F_label := sb "reac-pw.conf.d/%u-x.conf".
Definition F_probe := sb "%sx".
Definition S_base := sb "reac-pw.conf".
Definition S_segment := sb "segment".
Definition S_role := sb "role".
Definition S_model := sb "model".
Definition S_ignore := sb "ignore".
Definition S_knock := sb "knock".
Definition S_yes := sb "yes".
Definition S_true := sb "true".
Definition S_no := sb "no".
Definition S_false := sb "false".
Definition S_auto := sb "auto".
Definition S_master := sb "master".
Definition S_slave := sb "slave".
Definition S_tap := sb "tap".
Definition S_box := sb "box".
Definition S_nosuch := sb "nosuch0".
Definition S_enp := sb "enp1s0".
Definition TNP := sb "takes no plan".
(** The 17 refusal formats of R: (R:147 ... R:319), byte for byte. *)
Definition F_long := sb "line is longer than %zu bytes and was NOT read".
Definition F_notclosed := sb "section is not closed: '%s'".
Definition F_after := sb "text after the closing ']' of '%s'".
Definition F_noname := sb "[segment] names no segment".
Definition F_toolong := sb "[segment %s] is longer than an interface name can be (%d)".
Definition F_bound := sb "[segment %s] is past the %d-segment bound and was NOT read".
Definition F_twice := sb "[segment %s] appears more than once in this file; the keys are merged".
Definition F_neither := sb "'%s' is neither a [segment <name>] header nor a key = value".
Definition F_outside := sb "'%s' is outside any [segment <name>] section".
Definition F_badrole := sb "[segment %s] role = '%s' is not one of auto|master|slave|tap|box".
Definition F_badignore := sb "[segment %s] ignore = '%s' is not yes|no".
Definition F_knock := sb "[segment %s] knock takes no plan since 1.0.41: the knock has one content, the control frames, never the stream; remove the line (it says '%.24s')".
Definition F_xmodel := sb "[segment %s] model = '%s' is meaningful only under role = box; the role stands and the model is dropped".
Local Close Scope string_scope.
Definition F_unknown := sb "unknown section [%s] "%string ++ EMDASH ++ sb " only [segment <name>] is understood"%string.
Definition F_badmodel := sb "[segment %s] model = '%s' is not a box model "%string ++ EMDASH ++ sb " %s"%string.
Definition F_nokey := sb "[segment %s] has no key '%s' "%string ++ EMDASH ++ sb " role, model, ignore"%string.
Definition F_xbox := sb "[segment %s] role = box needs a model "%string ++ EMDASH ++ sb " none was given, so the segment falls back to auto"%string.

(** ** 3. The box-model table (K:12-35), shared by both texts: the reader reaches it through
    reac_box_catalogue_by_token (K:47-50) and reac_box_catalogue (K:38-43). *)
Definition cat_toks : list (list Z) :=
  map sb ["s1608"; "s0808"; "s4000s"; "s4000s-0832"; "s0816"; "s2416"; "s4000d"; "s4000m"; "fr4000"; "fr0040";
          "fr2020"]%string.
(** fuzz_catalogue_row(s, n), the n bytes at s being t: the first row whose token is t ([strlen(tok) == n &&
    memcmp(tok, s, n) == 0]). *)
Fixpoint row_go (toks : list (list Z)) (t : list Z) (i : nat) : option nat :=
  match toks with
  | [] => None
  | k :: r => if (length k =? length t)%nat && leqb k t then Some i else row_go r t (S i)
  end.
Definition cat_row (t : list Z) : option nat := row_go cat_toks t 0.
(** reac_box_catalogue_by_token(token) = fuzz_catalogue_row(token, strlen(token)). *)
Definition by_token (token : list Z) : option nat := cat_row (cut_nul token).

(** ** 4. The payload (F:26-97, H:579-620) *)

Definition fuzz_u8 (inp : list Z) : Z * list Z := match inp with [] => (0, []) | b :: r => (b, r) end.
Definition fuzz_u16 (inp : list Z) : Z * list Z :=
  let (lo, i1) := fuzz_u8 inp in
  let (hi, i2) := fuzz_u8 i1 in
  (Z.land (Z.lor lo (Z.shiftl hi 8)) 65535, i2).
(** fuzz_take(in, want, &p): [n = min(want, in->n)]; p = the n bytes, the cursor moves past them. *)
Definition fuzz_take (inp : list Z) (want : Z) : list Z * list Z :=
  let n := Nat.min (Z.to_nat want) (length inp) in (firstn n inp, skipn n inp).
(** fuzz_str(p, n): the n bytes cut at their first NUL. *)
Definition fuzz_str (p : list Z) : list Z := cut_nul p.

Record file := File { f_lb : Z; f_text : list Z }.
Record payload := Payload { p_cap : Z; p_flags : Z; p_files : list file }.

Fixpoint dec_files (k : nat) (inp : list Z) : list file :=
  match k with
  | O => []
  | S k' =>
      let (lb, i1) := fuzz_u8 inp in
      let (len, i2) := fuzz_u16 i1 in
      let (p, i3) := fuzz_take i2 len in
      File lb (fuzz_str p) :: dec_files k' i3
  end.
(** H:584-586, 597-601. *)
Definition decode (data : list Z) : payload :=
  let (b0, i1) := fuzz_u8 data in
  let (flags, i2) := fuzz_u8 i1 in
  let (b2, i3) := fuzz_u8 i2 in
  Payload (b0 mod 40) flags (dec_files (Z.to_nat (1 + b2 mod 4)) i3).

(** The label of a drop-in (H:602-610): bit 7, the static 121-byte buffer of 120 'L'; else 0, none; else the
    snprintf into label[40]. *)
Definition longl : list Z := repeat 76 120.
Definition label_of (lb : Z) : option (list Z) :=
  if negb (Z.land lb 128 =? 0) then Some longl
  else if lb =? 0 then None
  else Some (snprintf_s 40 F_label [AI lb]).

(** The lines of a text, as both loops cut them (H:266-270, R:131-136): [nl = strchr(p, '\n')]; the line is the
    bytes before nl (or the rest); p moves past nl (or to the end). *)
Fixpoint break_nl (p : list Z) : list Z * list Z :=
  match p with
  | [] => ([], [])
  | b :: r => if b =? NL then ([], r) else let (l, q) := break_nl r in (b :: l, q)
  end.
Fixpoint lines_go (fuel : nat) (p : list Z) : list (list Z) :=
  match fuel with
  | O => []
  | S f => match p with [] => [] | _ => let (l, q) := break_nl p in l :: lines_go f q end
  end.
Definition lines (p : list Z) : list (list Z) := lines_go (S (length p)) p.

(** ** 5. The harness's model (H:81-371) *)

Record mseg := MSeg {
  ms_name : list Z; ms_role : Z; ms_role_set : bool; ms_ignore : bool; ms_ignore_set : bool;
  ms_model_set : bool; ms_model : list Z; ms_role_file : list Z; ms_ignore_file : list Z; ms_gen : Z }.
(** memset(g, 0) + memcpy(g->name, nm, n). *)
Definition mseg0 (name : list Z) : mseg := MSeg name 0 false false false false [] [] [] 0.
Definition mseg_d : mseg := mseg0 [].

(** struct mconf; [mc_kept] is kept[0 .. n_kept) with kept_knock[i] beside each. *)
Record mconf := MConf {
  mc_seg : list mseg; mc_overflow : Z; mc_refused : Z; mc_kept : list (list Z * bool); mc_gen : Z;
  mc_reading : list Z }.
Definition mconf0 : mconf := MConf [] 0 0 [] 0 [].

Definition m_set_segs (c : mconf) (s : list mseg) : mconf :=
  MConf s (mc_overflow c) (mc_refused c) (mc_kept c) (mc_gen c) (mc_reading c).
Fixpoint upd_nth {A} (i : nat) (f : A -> A) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | x :: r, O => f x :: r
  | x :: r, S i' => x :: upd_nth i' f r
  end.
Definition m_upd (c : mconf) (i : nat) (f : mseg -> mseg) : mconf := m_set_segs c (upd_nth i f (mc_seg c)).

Definition ms_with_gen (z : Z) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) (ms_ignore_set g) (ms_model_set g) (ms_model g)
       (ms_role_file g) (ms_ignore_file g) z.
Definition ms_with_role (r : Z) (file : list Z) (g : mseg) : mseg :=
  MSeg (ms_name g) r true (ms_ignore g) (ms_ignore_set g) (ms_model_set g) (ms_model g) file (ms_ignore_file g)
       (ms_gen g).
Definition ms_with_model (m : list Z) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) (ms_ignore_set g) true m (ms_role_file g)
       (ms_ignore_file g) (ms_gen g).
Definition ms_with_ignore (b : bool) (file : list Z) (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) b true (ms_model_set g) (ms_model g) (ms_role_file g) file (ms_gen g).
(** m_cross's two edits (H:303, H:306-307). *)
Definition ms_drop_model (g : mseg) : mseg :=
  MSeg (ms_name g) (ms_role g) (ms_role_set g) (ms_ignore g) (ms_ignore_set g) false (ms_model g) (ms_role_file g)
       (ms_ignore_file g) (ms_gen g).
Definition ms_drop_role (g : mseg) : mseg :=
  MSeg (ms_name g) 0 false (ms_ignore g) (ms_ignore_set g) (ms_model_set g) (ms_model g) (ms_role_file g)
       (ms_ignore_file g) (ms_gen g).

(** m_refuse (H:101-111); [knock] is H:251-252, which marks kept_knock[n_kept] just before the call. *)
Definition m_refuse (c : mconf) (line : Z) (knock : bool) : mconf :=
  let kept :=
    if Z.of_nat (length (mc_kept c)) <? 8 then
      mc_kept c ++ [(if 0 <? line then snprintf_s 112 F_addr_line [AS (mc_reading c); AI line]
                     else snprintf_s 112 F_addr [AS (mc_reading c)], knock)]
    else mc_kept c in
  MConf (mc_seg c) (mc_overflow c) (mc_refused c + 1) kept (mc_gen c) (mc_reading c).

(** strip (H:119-125) on [s, e): forward over the blanks, then back. *)
Definition h_strip (l : list Z) : list Z := rev (dropwhile blank (rev (dropwhile blank l))).
(** ieq(s, n, word) (H:127-138), the n bytes at s being l. *)
Fixpoint ieq_go (l w : list Z) : bool :=
  match l, w with
  | [], [] => true
  | a :: l', x :: w' => (lower a =? x) && ieq_go l' w'
  | _, _ => false
  end.
Definition ieq (l w : list Z) : bool := (length l =? length w)%nat && ieq_go l w.
(** fold(s, n, out, cap) (H:141-148): the first min(n, cap - 1) bytes, folded. *)
Definition h_fold (l : list Z) (cap : nat) : list Z := map lower (firstn (cap - 1) l).
(** m_find (H:150-156): [strlen(name_i) == n && memcmp(name_i, name, n) == 0]. *)
Fixpoint m_find_go (segs : list mseg) (name : list Z) (i : nat) : option nat :=
  match segs with
  | [] => None
  | g :: r => if (strlen (ms_name g) =? length name)%nat && leqb (firstn (length name) (ms_name g)) name
              then Some i else m_find_go r name (S i)
  end.
Definition m_find (c : mconf) (name : list Z) : option nat := m_find_go (mc_seg c) name 0.

(** m_header (H:159-194), l = the stripped line, '[' first. *)
Definition m_header (c : mconf) (l : list Z) (line : Z) : mconf * option nat :=
  match memchr l RBR with
  | None => (m_refuse c line false, None)
  | Some ci =>
    if negb (S ci =? length l)%nat then (m_refuse c line false, None) else
    let b := h_strip (slice 1 ci l) in
    if (length b <? 8)%nat || negb (ieq (firstn 7 b) S_segment) || negb (sp_tab (nth 7 b 0))
    then (m_refuse c line false, None) else
    let nm := h_strip (skipn 7 b) in
    let n := length nm in
    if (n =? 0)%nat || (16 <=? n)%nat then (m_refuse c line false, None) else
    match m_find c nm with
    | None =>
        if (32 <=? length (mc_seg c))%nat then
          (m_refuse (MConf (mc_seg c) (mc_overflow c + 1) (mc_refused c) (mc_kept c) (mc_gen c) (mc_reading c))
                    line false, None)
        else (m_set_segs c (mc_seg c ++ [ms_with_gen (mc_gen c) (mseg0 nm)]), Some (length (mc_seg c)))
    | Some i =>
        let c1 := if ms_gen (nth i (mc_seg c) mseg_d) =? mc_gen c then m_refuse c line false else c in
        (m_upd c1 i (ms_with_gen (mc_gen c)), Some i)
    end
  end.

(** The role words of H:214-218 and the role of each (enum reac_role_intent, RR:61-86). *)
Fixpoint word_go (words : list (list Z)) (low : list Z) (i : Z) : option Z :=
  match words with
  | [] => None
  | w :: r => if (length w =? length low)%nat && leqb (firstn (length low) w) low then Some i
              else word_go r low (i + 1)
  end.
Definition h_role_word (low : list Z) : option Z := word_go [S_auto; S_master; S_slave; S_tap; S_box] low 0.
(** H:207-210: one pair of matching quotes. *)
Definition h_unquote (v : list Z) : list Z :=
  if (2 <=? length v)%nat && ((hd0 v =? DQ) || (hd0 v =? SQ)) && (last v 0 =? hd0 v)
  then removelast (tl v) else v.

(** m_key (H:197-257), l = the stripped line. *)
Definition m_key (c : mconf) (g : option nat) (l : list Z) (line : Z) : mconf :=
  match memchr l EQ, g with
  | Some ei, Some gi =>
    let k := h_strip (firstn ei l) in
    let v := h_unquote (h_strip (skipn (S ei) l)) in
    if ieq k S_role then
      match h_role_word (h_fold v 64) with
      | Some r => m_upd c gi (ms_with_role r (snprintf_s 96 F_s [AS (mc_reading c)]))
      | None => m_refuse c line false
      end
    else if ieq k S_model then
      let low := h_fold v 24 in
      match cat_row low with
      | None => m_refuse c line false
      | Some _ => m_upd c gi (ms_with_model low)
      end
    else if ieq k S_ignore then
      if ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49)) then
        m_upd c gi (ms_with_ignore true (snprintf_s 96 F_s [AS (mc_reading c)]))
      else if ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48)) then
        m_upd c gi (ms_with_ignore false (snprintf_s 96 F_s [AS (mc_reading c)]))
      else m_refuse c line false
    else if ieq k S_knock then m_refuse c line true
    else m_refuse c line false
  | _, _ => m_refuse c line false
  end.

(** H:280-284: the first '#' or ';' at the start of the line or after a space or a tab ends it. *)
Fixpoint h_cut_go (first : bool) (prev : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | q :: r => if is_mark q && (first || sp_tab prev) then [] else q :: h_cut_go false q r
  end.
Definition h_cut_comment (l : list Z) : list Z := h_cut_go true 0 l.

(** One line of m_file (H:266-291), its number [line]. *)
Definition m_line (st : mconf * option nat) (line : Z) (l : list Z) : mconf * option nat :=
  let (c, cur) := st in
  if (512 <=? length l)%nat then
    let f := dropwhile blank l in
    ((m_refuse c line false), if hd0 f =? LBR then None else cur)
  else
    let s := h_strip (h_cut_comment l) in
    match s with
    | [] => (c, cur)
    | b :: _ => if b =? LBR then m_header c s line else (m_key c cur s line, cur)
    end.
Fixpoint m_lines (st : mconf * option nat) (n : Z) (ls : list (list Z)) : mconf * option nat :=
  match ls with [] => st | l :: r => m_lines (m_line st (n + 1) l) (n + 1) r end.
(** m_file (H:259-293). *)
Definition m_file (c : mconf) (text : list Z) (label : option (list Z)) : mconf :=
  let rd := snprintf_s 96 F_s [AS (match label with Some l => l | None => S_base end)] in
  let c1 := MConf (mc_seg c) (mc_overflow c) (mc_refused c) (mc_kept c) (mc_gen c + 1) rd in
  fst (m_lines (c1, None) 0 (lines text)).

(** m_cross (H:296-310). *)
Definition m_cross_seg (c : mconf) (i : nat) : mconf :=
  let g := nth i (mc_seg c) mseg_d in
  let box := ms_role_set g && (ms_role g =? 4) in
  if ms_model_set g && negb box then m_upd (m_refuse c 0 false) i ms_drop_model
  else if box && negb (ms_model_set g) then m_upd (m_refuse c 0 false) i ms_drop_role
  else c.
Definition m_cross (c : mconf) : mconf := fold_left m_cross_seg (seq 0 (length (mc_seg c))) c.

(** m_split (H:323-350): the digit loop with its early exit. *)
Fixpoint m_digits (l : list Z) (vid : Z) : option Z :=
  match l with
  | [] => Some vid
  | q :: r => if (q <? 48) || (57 <? q) then None else
              let v := vid * 10 + (q - 48) in if 4094 <? v then None else m_digits r v
  end.
Definition h_parent_ok (ch : Z) : bool :=
  ((97 <=? ch) && (ch <=? 122)) || ((65 <=? ch) && (ch <=? 90)) || ((48 <=? ch) && (ch <=? 57)) ||
  (ch =? 46) || (ch =? 45) || (ch =? 58) || (ch =? 95).
Definition m_split (name : list Z) : option (list Z * Z) :=
  match strrchr name DOT with
  | None => None
  | Some di =>
    if (di =? 0)%nat || (hd0 (skipn (S di) name) =? 0) then None else
    match m_digits (skipn (S di) name) 0 with
    | None => None
    | Some vid => if vid <? 1 then None else
                  if forallb h_parent_ok (firstn di name) then Some (firstn di name, vid) else None
    end
  end.
(** m_declared (H:353-371) over a table [tab] of (parent, vid). *)
Fixpoint m_decl_go (segs : list mseg) (tab : list (list Z * Z)) (cap added : Z) : Z * list (list Z * Z) :=
  match segs with
  | [] => (added, tab)
  | g :: r =>
    if ms_ignore g then m_decl_go r tab cap added else
    match m_split (ms_name g) with
    | None => m_decl_go r tab cap added
    | Some (p, v) =>
      if existsb (fun e => (snd e =? v) && (strcmp (fst e) p =? 0)) tab then m_decl_go r tab cap added
      else if cap <=? Z.of_nat (length tab) then (-1, tab)
      else m_decl_go r (tab ++ [(p, v)]) cap (added + 1)
    end
  end.
Definition m_declared (c : mconf) (tab : list (list Z * Z)) (cap : Z) : Z * list (list Z * Z) :=
  m_decl_go (mc_seg c) tab cap 0.

(** ** 6. The reader's model (R:19-332, R:517-580, V:20-80, RR:110-120) *)

Record rseg := RSeg {
  rs_name : list Z; rs_role : Z; rs_role_set : bool; rs_ignore : bool; rs_ignore_set : bool;
  rs_model : list Z; rs_model_set : bool; rs_model_file : list Z; rs_role_file : list Z;
  rs_ignore_file : list Z; rs_seen_gen : Z }.
Definition rseg0 (name : list Z) : rseg := RSeg name 0 false false false [] false [] [] [] 0.
Definition rseg_d : rseg := rseg0 [].

(** struct reac_segconf, the fields the parse writes; [rc_refusal] is refusal[0 .. n_refusals). *)
Record rconf := RConf {
  rc_seg : list rseg; rc_refusal : list (list Z); rc_refused : Z; rc_overflow : Z; rc_reading : list Z;
  rc_gen : Z }.
(** reac_segconf_init (R:19-22): all zero. *)
Definition rconf0 : rconf := RConf [] [] 0 0 [] 0.

Definition r_set_segs (c : rconf) (s : list rseg) : rconf :=
  RConf s (rc_refusal c) (rc_refused c) (rc_overflow c) (rc_reading c) (rc_gen c).
Definition r_upd (c : rconf) (i : nat) (f : rseg -> rseg) : rconf := r_set_segs c (upd_nth i f (rc_seg c)).

Definition rs_with_gen (z : Z) (s : rseg) : rseg :=
  RSeg (rs_name s) (rs_role s) (rs_role_set s) (rs_ignore s) (rs_ignore_set s) (rs_model s) (rs_model_set s)
       (rs_model_file s) (rs_role_file s) (rs_ignore_file s) z.
Definition rs_with_role (r : Z) (file : list Z) (s : rseg) : rseg :=
  RSeg (rs_name s) r true (rs_ignore s) (rs_ignore_set s) (rs_model s) (rs_model_set s) (rs_model_file s) file
       (rs_ignore_file s) (rs_seen_gen s).
Definition rs_with_model (m file : list Z) (s : rseg) : rseg :=
  RSeg (rs_name s) (rs_role s) (rs_role_set s) (rs_ignore s) (rs_ignore_set s) m true file (rs_role_file s)
       (rs_ignore_file s) (rs_seen_gen s).
Definition rs_with_ignore (b : bool) (file : list Z) (s : rseg) : rseg :=
  RSeg (rs_name s) (rs_role s) (rs_role_set s) b true (rs_model s) (rs_model_set s) (rs_model_file s)
       (rs_role_file s) file (rs_seen_gen s).
(** cross_check's two edits (R:312-313, R:321-322). *)
Definition rs_drop_model (s : rseg) : rseg :=
  RSeg (rs_name s) (rs_role s) (rs_role_set s) (rs_ignore s) (rs_ignore_set s) [] false (rs_model_file s)
       (rs_role_file s) (rs_ignore_file s) (rs_seen_gen s).
Definition rs_drop_role (s : rseg) : rseg :=
  RSeg (rs_name s) 0 false (rs_ignore s) (rs_ignore_set s) (rs_model s) (rs_model_set s) (rs_model_file s)
       (rs_role_file s) (rs_ignore_file s) (rs_seen_gen s).

(** refuse (R:30-48): counted always; kept while n_refusals < 8 and the address fits (k < 200). The text kept is
    the address and then vsnprintf's text, cut to the 200-byte slot. *)
Definition r_where (c : rconf) : list Z := if hd0 (rc_reading c) =? 0 then S_base else rc_reading c.
Definition r_addr_fmt (line : Z) : list Z := if 0 <? line then F_addr_line else F_addr.
Definition r_addr_args (c : rconf) (line : Z) : list arg :=
  if 0 <? line then [AS (r_where c); AI line] else [AS (r_where c)].
Definition refuse (c : rconf) (line : Z) (f : list Z) (a : list arg) : rconf :=
  let c1 := RConf (rc_seg c) (rc_refusal c) (rc_refused c + 1) (rc_overflow c) (rc_reading c) (rc_gen c) in
  if 8 <=? Z.of_nat (length (rc_refusal c)) then c1 else
  let k := snprintf_r (r_addr_fmt line) (r_addr_args c line) in
  if (k <? 0) || (200 <=? k) then c1 else
  RConf (rc_seg c) (rc_refusal c ++ [snprintf_s 200 (r_addr_fmt line) (r_addr_args c line) ++
                                     snprintf_s (200 - k) f a])
        (rc_refused c + 1) (rc_overflow c) (rc_reading c) (rc_gen c).

(** trim (R:50-59): past the leading blanks; e = s + strlen(s); back over the trailing blanks; *e = 0. *)
Fixpoint trim_end (s : list Z) (e fuel : nat) : nat :=
  match fuel with
  | O => e
  | S f => match e with O => O | S e' => if blank (nth e' s 0) then trim_end s e' f else e end
  end.
Definition r_trim (s : list Z) : list Z :=
  let s1 := dropwhile blank (cut_nul s) in firstn (trim_end s1 (length s1) (length s1)) s1.
(** strip_comment (R:65-74): the first index p with a mark and p == s or p[-1] a space or a tab. *)
Definition r_comment_at (s : list Z) (i : nat) : bool :=
  is_mark (nth i s 0) && ((i =? 0)%nat || sp_tab (nth (i - 1) s 0)).
Fixpoint first_at (P : nat -> bool) (i fuel : nat) : option nat :=
  match fuel with O => None | S f => if P i then Some i else first_at P (S i) f end.
Definition r_strip_comment (s : list Z) : list Z :=
  let s1 := cut_nul s in
  match first_at (r_comment_at s1) 0 (length s1) with Some i => firstn i s1 | None => s1 end.
(** unquote (R:78-86). *)
Definition r_unquote (v : list Z) : list Z :=
  let n := strlen v in
  if (2 <=? n)%nat && (((nth 0 v 0 =? DQ) && (nth (n - 1) v 0 =? DQ)) || ((nth 0 v 0 =? SQ) && (nth (n - 1) v 0 =? SQ)))
  then slice 1 (n - 1) v else cut_nul v.
(** parse_bool (R:88-99). *)
Definition parse_bool (v : list Z) : option bool :=
  if (strcasecmp v S_yes =? 0) || (strcasecmp v S_true =? 0) || (strcmp v [49] =? 0) then Some true
  else if (strcasecmp v S_no =? 0) || (strcasecmp v S_false =? 0) || (strcmp v [48] =? 0) then Some false
  else None.
(** reac_role_intent_parse (RR:110-120). *)
Definition role_intent_parse (s : list Z) : option Z :=
  if strcmp s S_auto =? 0 then Some 0 else if strcmp s S_master =? 0 then Some 1
  else if strcmp s S_slave =? 0 then Some 2 else if strcmp s S_tap =? 0 then Some 3
  else if strcmp s S_box =? 0 then Some 4 else None.
(** The fold loops of R:236-238 and R:254-256: [for (q = val; *q && li + 1 < sizeof low; q++, li++)]. *)
Fixpoint r_low (v : list Z) (li cap : nat) : list Z :=
  match v with
  | [] => []
  | q :: r => if q =? 0 then [] else if (li + 1 <? cap)%nat then lower q :: r_low r (S li) cap else []
  end.
(** The list of tokens of R:258-263: [for (ti = 0; ti < ntok && kn + 2 < sizeof known; ti++)
    kn += snprintf(known + kn, sizeof known - kn, "%s%s", ti ? "|" : "", tab[ti].token);]. *)
Fixpoint known_go (toks : list (list Z)) (first : bool) (kn : Z) (acc : list Z) : list Z :=
  match toks with
  | [] => acc
  | t :: r =>
    if kn + 2 <? 240 then
      let a := [AS (if first then [] else [124]); AS t] in
      known_go r false (kn + snprintf_r F_ss a) (firstn (Z.to_nat kn) acc ++ snprintf_s (240 - kn) F_ss a)
    else acc
  end.
Definition known : list Z := known_go cat_toks true 0 [].

(** seg_get (R:103-118): [strcmp] over the table, then a new entry if there is room. *)
Fixpoint r_find_go (segs : list rseg) (name : list Z) (i : nat) : option nat :=
  match segs with
  | [] => None
  | s :: r => if strcmp (rs_name s) name =? 0 then Some i else r_find_go r name (S i)
  end.
Definition seg_get (c : rconf) (name : list Z) : rconf * option (nat * bool) :=
  match r_find_go (rc_seg c) name 0 with
  | Some i => (c, Some (i, false))
  | None =>
    if (32 <=? length (rc_seg c))%nat then
      (RConf (rc_seg c) (rc_refusal c) (rc_refused c) (rc_overflow c + 1) (rc_reading c) (rc_gen c), None)
    else (r_set_segs c (rc_seg c ++ [rseg0 (snprintf_s 16 F_s [AS name])]), Some (length (rc_seg c), true))
  end.

(** The header branch of reac_segconf_parse_file (R:159-213), [line] the trimmed line, '[' first. *)
Definition r_header (c : rconf) (cur_name : list Z) (lineno : Z) (line : list Z) : rconf * option nat * list Z :=
  match strchr line RBR with
  | None => (refuse c lineno F_notclosed [AS line], None, cur_name)
  | Some ci =>
    if negb (nth (S ci) line 0 =? 0) then (refuse c lineno F_after [AS line], None, cur_name) else
    let body := r_trim (slice 1 ci line) in
    if negb (strncasecmp body S_segment 7 =? 0) || negb (sp_tab (nth 7 body 0))
    then (refuse c lineno F_unknown [AS body], None, cur_name) else
    let name := r_trim (skipn 7 body) in
    if hd0 name =? 0 then (refuse c lineno F_noname [], None, cur_name) else
    if (16 <=? strlen name)%nat then (refuse c lineno F_toolong [AS name; AI 15], None, cur_name) else
    match seg_get c name with
    | (c1, None) => (refuse c1 lineno F_bound [AS name; AI 32], None, cur_name)
    | (c1, Some (i, is_new)) =>
      let c2 := if negb is_new && (rs_seen_gen (nth i (rc_seg c1) rseg_d) =? rc_gen c1)
                then refuse c1 lineno F_twice [AS name] else c1 in
      (r_upd c2 i (rs_with_gen (rc_gen c2)), Some i, snprintf_s 16 F_s [AS name])
    end
  end.
(** The key branch (R:215-293), [line] the trimmed line; the section is [cur]. *)
Definition r_key (c : rconf) (cur : option nat) (cur_name : list Z) (lineno : Z) (line : list Z)
  : rconf * option nat * list Z :=
  match strchr line EQ with
  | None => (refuse c lineno F_neither [AS line], cur, cur_name)
  | Some ei =>
    let key := r_trim (firstn ei line) in
    let val := r_unquote (r_trim (skipn (S ei) line)) in
    match cur with
    | None => (refuse c lineno F_outside [AS key], cur, cur_name)
    | Some gi =>
      if strcasecmp key S_role =? 0 then
        match role_intent_parse (r_low val 0 64) with
        | None => (refuse c lineno F_badrole [AS cur_name; AS val], cur, cur_name)
        | Some r => (r_upd c gi (rs_with_role r (snprintf_s 96 F_s [AS (rc_reading c)])), cur, cur_name)
        end
      else if strcasecmp key S_model =? 0 then
        let low := r_low val 0 24 in
        match by_token low with
        | None => (refuse c lineno F_badmodel [AS cur_name; AS val; AS known], cur, cur_name)
        | Some _ => (r_upd c gi (rs_with_model (snprintf_s 24 F_s [AS low]) (snprintf_s 96 F_s [AS (rc_reading c)])),
                     cur, cur_name)
        end
      else if strcasecmp key S_ignore =? 0 then
        match parse_bool val with
        | None => (refuse c lineno F_badignore [AS cur_name; AS val], cur, cur_name)
        | Some b => (r_upd c gi (rs_with_ignore b (snprintf_s 96 F_s [AS (rc_reading c)])), cur, cur_name)
        end
      else if strcasecmp key S_knock =? 0 then (refuse c lineno F_knock [AS cur_name; AS val], cur, cur_name)
      else (refuse c lineno F_nokey [AS cur_name; AS key], cur, cur_name)
    end
  end.
(** One line of reac_segconf_parse_file (R:131-294); [cur_name] is R:127's buffer. *)
Definition r_line (c : rconf) (cur : option nat) (cur_name : list Z) (lineno : Z) (at_ : list Z)
  : rconf * option nat * list Z :=
  let len := length at_ in
  if (512 <=? len)%nat then
    let lead := strspn_blank at_ in
    (refuse c lineno F_long [AI 511], (if (lead <? len)%nat && (nth lead at_ 0 =? LBR) then None else cur), cur_name)
  else
  let line := r_trim (r_strip_comment at_) in
  if hd0 line =? 0 then (c, cur, cur_name)
  else if hd0 line =? LBR then r_header c cur_name lineno line
  else r_key c cur cur_name lineno line.
Fixpoint r_lines (st : rconf * option nat * list Z) (n : Z) (ls : list (list Z)) : rconf * option nat * list Z :=
  match ls with
  | [] => st
  | l :: r => let '(c, cur, nm) := st in r_lines (r_line c cur nm (n + 1) l) (n + 1) r
  end.
(** reac_segconf_parse_file (R:120-296), text not NULL; returns c->n. *)
Definition r_parse_file (c : rconf) (text : list Z) (label : option (list Z)) : rconf * Z :=
  let rd := snprintf_s 96 F_s [AS (match label with Some l => l | None => S_base end)] in
  let c1 := RConf (rc_seg c) (rc_refusal c) (rc_refused c) (rc_overflow c) rd (rc_gen c + 1) in
  let '(c2, _, _) := r_lines (c1, None, []) 0 (lines text) in
  (c2, Z.of_nat (length (rc_seg c2))).
(** cross_check (R:303-325). *)
Definition r_cross_seg (c : rconf) (i : nat) : rconf :=
  let s := nth i (rc_seg c) rseg_d in
  let is_box := rs_role_set s && (rs_role s =? 4) in
  if rs_model_set s && negb is_box then r_upd (refuse c 0 F_xmodel [AS (rs_name s); AS (rs_model s)]) i rs_drop_model
  else if is_box && negb (rs_model_set s) then r_upd (refuse c 0 F_xbox [AS (rs_name s)]) i rs_drop_role
  else c.
Definition cross_check (c : rconf) : rconf := fold_left r_cross_seg (seq 0 (length (rc_seg c))) c.
(** reac_segconf_parse (R:327-332). *)
Definition r_parse (c : rconf) (text : list Z) : rconf * Z :=
  let (c1, n) := r_parse_file c text (Some S_base) in (cross_check c1, n).

(** The accessors (R:517-559); [None] is NULL, and r_role's [Some r] is "returns 1 and *out = r". *)
Definition r_find (c : rconf) (name : list Z) : option nat := r_find_go (rc_seg c) name 0.
Definition r_seg (c : rconf) (i : nat) : rseg := nth i (rc_seg c) rseg_d.
Definition r_ignored (c : rconf) (name : list Z) : bool :=
  match r_find c name with Some i => rs_ignore (r_seg c i) | None => false end.
Definition r_role (c : rconf) (name : list Z) : option Z :=
  match r_find c name with Some i => if rs_role_set (r_seg c i) then Some (rs_role (r_seg c i)) else None | None => None end.
Definition r_role_file (c : rconf) (name : list Z) : option (list Z) :=
  match r_find c name with
  | Some i => if rs_role_set (r_seg c i) && negb (hd0 (rs_role_file (r_seg c i)) =? 0) then Some (rs_role_file (r_seg c i)) else None
  | None => None
  end.
Definition r_ignore_file (c : rconf) (name : list Z) : option (list Z) :=
  match r_find c name with
  | Some i => if rs_ignore_set (r_seg c i) && negb (hd0 (rs_ignore_file (r_seg c i)) =? 0) then Some (rs_ignore_file (r_seg c i)) else None
  | None => None
  end.
Definition r_model (c : rconf) (name : list Z) : option (list Z) :=
  match r_find c name with Some i => if rs_model_set (r_seg c i) then Some (rs_model (r_seg c i)) else None | None => None end.

(** name_ok (V:20-30). *)
Definition name_ok (s : list Z) : bool :=
  match cut_nul s with
  | [] => false
  | s1 => forallb (fun ch => isalnum ch || (ch =? 46) || (ch =? 45) || (ch =? 58) || (ch =? 95)) s1
  end.
(** reac_declared_vlan_split (V:32-62), cap = IFNAMSIZ = 16; the vid is the uint16_t store. *)
Definition vlan_split (seg : list Z) : option (list Z * Z) :=
  match strrchr seg DOT with
  | None => None
  | Some di =>
    if (di =? 0)%nat || (hd0 (skipn (S di) seg) =? 0) then None else
    let tail := cut_nul (skipn (S di) seg) in
    if negb (forallb isdigit tail) then None else
    let v := strtol10 tail in
    if (v <? 1) || (4094 <? v) then None else
    if (16 <? di + 1)%nat || (16 <? di + 1)%nat then None else
    if (16 <? strlen seg + 1)%nat then None else
    let parent := firstn di seg in
    if negb (name_ok parent) then None else Some (parent, v mod 65536)
  end.
(** reac_declared_vlan_add (V:65-80): 0 for a duplicate (first match), -1 when full, else memset + strncpy(15). *)
Definition vlan_add (tab : list (list Z * Z)) (max : Z) (parent : list Z) (vid : Z) : Z * list (list Z * Z) :=
  if existsb (fun e => (snd e =? vid) && (strcmp (fst e) parent =? 0)) tab then (0, tab)
  else if max <=? Z.of_nat (length tab) then (-1, tab)
  else (1, tab ++ [(firstn 15 (cut_nul parent), vid)]).
(** reac_segconf_declared (R:561-580). *)
Fixpoint r_decl_go (segs : list rseg) (tab : list (list Z * Z)) (max added : Z) : Z * list (list Z * Z) :=
  match segs with
  | [] => (added, tab)
  | s :: r =>
    if rs_ignore s then r_decl_go r tab max added else
    match vlan_split (rs_name s) with
    | None => r_decl_go r tab max added
    | Some (p, v) =>
      let (rv, tab') := vlan_add tab max p v in
      if rv <? 0 then (-1, tab') else r_decl_go r tab' max (added + rv)
    end
  end.
Definition r_declared (c : rconf) (tab : list (list Z * Z)) (max : Z) : Z * list (list Z * Z) :=
  r_decl_go (rc_seg c) tab max 0.

(** ** 7. The run (H:587-620) and the checks (H:375-577, 622-665) *)

(** The file loop: every file but the last is a drop-in under its label, the last is the hand-written file;
    [returned] is H:596, 613, 617. *)
Fixpoint run_files (fs : list file) (c : rconf) (m : mconf) (ret : bool) : rconf * mconf * bool :=
  match fs with
  | [] => (c, m, ret)
  | [f] =>
    let m1 := m_cross (m_file m (f_text f) None) in
    let (c1, n) := r_parse c (f_text f) in
    (c1, m1, ret && (n =? Z.of_nat (length (mc_seg m1))))
  | f :: r =>
    let l := label_of (f_lb f) in
    let m1 := m_file m (f_text f) l in
    let (c1, n) := r_parse_file c (f_text f) l in
    run_files r c1 m1 (ret && (n =? Z.of_nat (length (mc_seg m1))))
  end.
Definition run (p : payload) : rconf * mconf * bool := run_files (p_files p) rconf0 mconf0 true.

Definition same_text (got want : option (list Z)) : bool :=
  match got, want with
  | None, None => true
  | Some a, Some b => strcmp a b =? 0
  | _, _ => false
  end.
Fixpoint forallb2 {A B} (P : A -> B -> bool) (l1 : list A) (l2 : list B) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => P a b && forallb2 P r1 r2
  | _, _ => false
  end.

(** check_segments (H:392-400, 407-429). *)
Definition check_segments (c : rconf) (m : mconf) (returned : bool) : bool :=
  (length (rc_seg c) =? length (mc_seg m))%nat && (rc_overflow c =? mc_overflow m) &&
  forallb2 (fun s g => strcmp (rs_name s) (ms_name g) =? 0) (firstn (length (mc_seg m)) (rc_seg c)) (mc_seg m) &&
  returned.
(** check_role, check_model, check_ignore, check_provenance (H:431-500) for one segment g of the model. *)
Definition check_seg (c : rconf) (g : mseg) : bool :=
  let nm := ms_name g in
  (match r_role c nm with
   | Some r => ms_role_set g && (r =? ms_role g)
   | None => negb (ms_role_set g)
   end) &&
  same_text (r_model c nm) (if ms_model_set g then Some (ms_model g) else None) &&
  Bool.eqb (r_ignored c nm) (ms_ignore g) &&
  same_text (r_role_file c nm) (if ms_role_set g then Some (ms_role_file g) else None) &&
  same_text (r_ignore_file c nm) (if ms_ignore_set g then Some (ms_ignore_file g) else None).
(** check_refusals (H:516-529). *)
Definition check_refusals (c : rconf) (m : mconf) : bool :=
  (rc_refused c =? mc_refused m) && (length (rc_refusal c) =? length (mc_kept m))%nat.
(** check_address and check_knock_refused (H:502-514, 531-542) for the i-th pair. *)
Definition check_kept (got : list Z) (want : list Z * bool) : bool :=
  (strncmp got (fst want) (strlen (fst want)) =? 0) && (negb (snd want) || strstr_found got TNP).
Fixpoint check_kept_all (gots : list (list Z)) (wants : list (list Z * bool)) : bool :=
  match gots, wants with
  | g :: gs, w :: ws => check_kept g w && check_kept_all gs ws
  | _, _ => true
  end.
(** check_absent (H:544-554). *)
Definition absent (c : rconf) (name : list Z) : bool :=
  match r_find c name, r_role c name, r_ignored c name, r_model c name with
  | None, None, false, None => true
  | _, _, _, _ => false
  end.
Definition probe_ok (c : rconf) (m : mconf) (probe : list Z) : bool :=
  match m_find m probe with None => absent c probe | Some _ => true end.
(** vlans_are (H:375-388): the guard entry tab[cap] is untouched iff the reader wrote no entry at or past cap,
    which the table model states as [length tab <= cap]. *)
Definition vlans_are (got want : Z * list (list Z * Z)) (cap : Z) : bool :=
  (fst got =? fst want) && (length (snd got) =? length (snd want))%nat &&
  forallb2 (fun e e' => (snd e =? snd e') && (strcmp (fst e) (fst e') =? 0)) (snd got) (snd want) &&
  (Z.of_nat (length (snd got)) <=? cap).
Definition vlan_init (p : payload) : list (list Z * Z) :=
  if negb (Z.land (p_flags p) 1 =? 0) && (0 <? p_cap p) then [(S_enp, 33)] else [].

(** Every check of LLVMFuzzerTestOneInput, in its order: [harness_ok p = true] iff no check_* aborts. *)
Definition harness_ok (p : payload) : bool :=
  let '(c, m, ret) := run p in
  check_segments c m ret &&
  forallb (check_seg c) (mc_seg m) &&
  check_refusals c m &&
  check_kept_all (rc_refusal c) (mc_kept m) &&
  forallb (fun g => probe_ok c m (snprintf_s 18 F_probe [AS (ms_name g)])) (mc_seg m) &&
  probe_ok c m S_nosuch &&
  vlans_are (r_declared c (vlan_init p) (p_cap p)) (m_declared m (vlan_init p) (p_cap p)) (p_cap p).

(** THE AGREEMENT THEOREM (statement): on every input of bytes, no check aborts. *)
Definition segconf_agreement : Prop :=
  forall data : list Z, Forall (fun b => 0 <= b < 256) data -> harness_ok (decode data) = true.

(** ** 8. Lemmas: lists and C strings *)

Lemma nulfree_nil : nulfree [].
Proof. intros []. Qed.
Lemma nulfree_cons a l : nulfree (a :: l) <-> a <> 0 /\ nulfree l.
Proof.
  unfold nulfree; cbn; split.
  - intros H; split; [intros E; apply H; left; congruence | intros Hi; apply H; right; exact Hi].
  - intros [Ha Hl] [E|Hi]; [congruence | exact (Hl Hi)].
Qed.
Lemma nulfree_app a b : nulfree (a ++ b) <-> nulfree a /\ nulfree b.
Proof. unfold nulfree; rewrite in_app_iff; tauto. Qed.
Lemma nulfree_firstn n l : nulfree l -> nulfree (firstn n l).
Proof. intros H. rewrite <- (firstn_skipn n l) in H. apply nulfree_app in H. tauto. Qed.
Lemma nulfree_skipn n l : nulfree l -> nulfree (skipn n l).
Proof. intros H. rewrite <- (firstn_skipn n l) in H. apply nulfree_app in H. tauto. Qed.
Lemma nulfree_rev l : nulfree l -> nulfree (rev l).
Proof. unfold nulfree; intros H Hi; apply H; apply in_rev; exact Hi. Qed.
Lemma nulfree_dropwhile P l : nulfree l -> nulfree (dropwhile P l).
Proof.
  induction l as [|a l IH]; cbn; intros H; [exact H|].
  destruct (P a); [apply IH; apply nulfree_cons in H; tauto | exact H].
Qed.
Lemma nulfree_tl l : nulfree l -> nulfree (tl l).
Proof. destruct l; cbn; [auto|]. intros H; apply nulfree_cons in H; tauto. Qed.
Lemma nulfree_removelast l : nulfree l -> nulfree (removelast l).
Proof.
  induction l as [|a l IH]; cbn; intros H; [exact H|]. apply nulfree_cons in H as [Ha Hl].
  destruct l; [apply nulfree_nil|]. apply nulfree_cons; split; auto.
Qed.
Lemma nulfree_map_lower l : nulfree l -> nulfree (map lower l).
Proof.
  induction l as [|a l IH]; cbn; intros H; [exact H|]. apply nulfree_cons in H as [Ha Hl].
  apply nulfree_cons; split; [|auto]. unfold lower. destruct ((65 <=? a) && (a <=? 90)) eqn:E; [|exact Ha].
  apply andb_true_iff in E as [E1 _]. apply Z.leb_le in E1. lia.
Qed.
Lemma nulfree_slice i j l : nulfree l -> nulfree (slice i j l).
Proof. intros H; apply nulfree_firstn, nulfree_skipn, H. Qed.
Lemma nulfree_h_strip l : nulfree l -> nulfree (h_strip l).
Proof. intros H; apply nulfree_rev, nulfree_dropwhile, nulfree_rev, nulfree_dropwhile, H. Qed.
Lemma nulfree_h_unquote l : nulfree l -> nulfree (h_unquote l).
Proof.
  intros H; unfold h_unquote. destruct (_ && _ && _); [|exact H]. apply nulfree_removelast, nulfree_tl, H.
Qed.
Lemma nulfree_h_cut l : forall f p, nulfree l -> nulfree (h_cut_go f p l).
Proof.
  induction l as [|a l IH]; intros f p H; cbn; [exact H|]. apply nulfree_cons in H as [Ha Hl].
  destruct (_ && _); [apply nulfree_nil|]. apply nulfree_cons; split; auto.
Qed.

Lemma cut_nul_id l : nulfree l -> cut_nul l = l.
Proof.
  induction l as [|a l IH]; cbn; intros H; [reflexivity|]. apply nulfree_cons in H as [Ha Hl].
  destruct (Z.eqb_spec a 0); [contradiction|]. rewrite IH; auto.
Qed.
Lemma cut_nul_nulfree l : nulfree (cut_nul l).
Proof.
  induction l as [|a l IH]; cbn; [apply nulfree_nil|].
  destruct (Z.eqb_spec a 0); [apply nulfree_nil|]. apply nulfree_cons; auto.
Qed.
Lemma cut_nul_len l : (length (cut_nul l) <= length l)%nat.
Proof. induction l as [|a l IH]; cbn; [lia|]. destruct (a =? 0); cbn; lia. Qed.
Lemma strlen_id l : nulfree l -> strlen l = length l.
Proof. intros H; unfold strlen; rewrite cut_nul_id; auto. Qed.
Lemma hd0_eq0 l : nulfree l -> (hd0 l =? 0) = (match l with [] => true | _ => false end).
Proof.
  destruct l as [|a l]; cbn; [reflexivity|]. intros H; apply nulfree_cons in H as [Ha _].
  apply Z.eqb_neq; exact Ha.
Qed.
Lemma nulfree_forallb l : forallb (fun x => negb (x =? 0)) l = true -> nulfree l.
Proof.
  induction l as [|a l IH]; cbn; intros H; [apply nulfree_nil|]. apply andb_true_iff in H as [H1 H2].
  apply nulfree_cons; split; [|auto]. intros ->; discriminate.
Qed.

Lemma strchr_memchr l c : nulfree l -> c <> 0 -> strchr l c = memchr l c.
Proof.
  induction l as [|a l IH]; cbn; intros H Hc; [reflexivity|]. apply nulfree_cons in H as [Ha Hl].
  destruct (a =? c); [reflexivity|]. destruct (Z.eqb_spec a 0); [contradiction|]. rewrite IH; auto.
Qed.
Lemma memchr_lt l c i : memchr l c = Some i -> (i < length l)%nat.
Proof.
  revert i; induction l as [|a l IH]; cbn; intros i H; [discriminate|].
  destruct (a =? c); [injection H as <-; lia|].
  destruct (memchr l c) as [k|] eqn:E; cbn in H; [|discriminate]. injection H as <-.
  specialize (IH k eq_refl). lia.
Qed.
Lemma nth_after_close l ci : nulfree l -> (ci < length l)%nat ->
  (nth (S ci) l 0 =? 0) = (S ci =? length l)%nat.
Proof.
  intros H Hlt. destruct (Nat.eq_dec (S ci) (length l)) as [E|E].
  - rewrite nth_overflow by lia. rewrite E, Nat.eqb_refl. reflexivity.
  - assert (Hin : In (nth (S ci) l 0) l) by (apply nth_In; lia).
    destruct (Z.eqb_spec (nth (S ci) l 0) 0) as [E0|E0]; [rewrite E0 in Hin; contradiction|].
    symmetry; apply Nat.eqb_neq; exact E.
Qed.

Lemma leqb_eq a b : leqb a b = true <-> a = b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; cbn; split; intros H; try discriminate; auto.
  - apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst; reflexivity.
  - injection H as -> ->. rewrite Z.eqb_refl. cbn. apply IH; reflexivity.
Qed.
Lemma leqb_refl a : leqb a a = true.
Proof. apply leqb_eq; reflexivity. Qed.
Lemma leqb_sym a b : leqb a b = leqb b a.
Proof.
  destruct (leqb a b) eqn:E1, (leqb b a) eqn:E2; auto.
  - apply leqb_eq in E1; subst; rewrite leqb_refl in E2; discriminate.
  - apply leqb_eq in E2; subst; rewrite leqb_refl in E1; discriminate.
Qed.
Lemma leqb_len a b : leqb a b = true -> length a = length b.
Proof. intros H; apply leqb_eq in H; subst; reflexivity. Qed.
Lemma len_leqb w l : (length w =? length l)%nat && leqb (firstn (length l) w) l = leqb w l.
Proof.
  destruct (Nat.eqb_spec (length w) (length l)) as [E|E]; cbn.
  - rewrite <- E, firstn_all. reflexivity.
  - destruct (leqb w l) eqn:H; [apply leqb_len in H; contradiction | reflexivity].
Qed.
Lemma leqb_single v x : leqb v [x] = (length v =? 1)%nat && (hd0 v =? x).
Proof.
  destruct v as [|a [|b v]]; cbn; [reflexivity| |].
  - rewrite andb_true_r. reflexivity.
  - rewrite andb_false_r. reflexivity.
Qed.
Lemma strcmp_refl a : strcmp a a = 0.
Proof.
  induction a as [|x a IH]; cbn; [reflexivity|]. rewrite Z.eqb_refl.
  destruct (x =? 0); cbn; [lia|exact IH].
Qed.
Lemma strcmp_eq a b : nulfree a -> nulfree b -> (strcmp a b =? 0) = leqb a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b] Ha Hb; cbn.
  - reflexivity.
  - apply nulfree_cons in Hb as [Hy _]. apply Z.eqb_neq; lia.
  - apply nulfree_cons in Ha as [Hx _]. apply Z.eqb_neq; exact Hx.
  - apply nulfree_cons in Ha as [Hx Ha]; apply nulfree_cons in Hb as [Hy Hb].
    destruct (Z.eqb_spec x y) as [<-|Hne]; cbn.
    + destruct (Z.eqb_spec x 0); [contradiction|]. cbn. apply IH; auto.
    + apply Z.eqb_neq; lia.
Qed.
Lemma strncmp_prefix p r : nulfree p -> strncmp (p ++ r) p (length p) = 0.
Proof.
  destruct p as [|a p]; cbn; intros H; [reflexivity|]. revert a H.
  induction p as [|b p IH]; intros a H; cbn; [lia|].
  apply nulfree_cons in H as [Ha H]. destruct (Z.eqb_spec a 0); [contradiction|].
  rewrite Z.eqb_refl. cbn. apply IH; exact H.
Qed.
Lemma prefixb_app n b : prefixb n (n ++ b) = true.
Proof. induction n as [|x n IH]; cbn; [reflexivity|]. rewrite Z.eqb_refl; exact IH. Qed.
Lemma infixb_unfold n h : infixb n h = prefixb n h || match h with [] => false | _ :: r => infixb n r end.
Proof. destruct h; reflexivity. Qed.
Lemma infixb_app a n b : infixb n (a ++ n ++ b) = true.
Proof.
  induction a as [|x a IH]; rewrite infixb_unfold; cbn [app].
  - rewrite prefixb_app; reflexivity.
  - rewrite IH, orb_true_r; reflexivity.
Qed.

Lemma firstn_S_snoc n l : (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  revert n; induction l as [|a l IH]; intros n H; cbn in H; [lia|].
  destruct n as [|n]; [reflexivity|]. change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l).
  rewrite (IH n) by lia. reflexivity.
Qed.
Lemma firstn_app_le (a b : list Z) n : (length a <= n)%nat -> firstn n (a ++ b) = a ++ firstn (n - length a) b.
Proof. intros H. rewrite firstn_app. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma removelast_firstn' (l : list Z) : removelast l = firstn (length l - 1) l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [removelast length].
  destruct l as [|b l]; [reflexivity|]. rewrite IH. cbn [length].
  replace (S (S (length l)) - 1)%nat with (S (length l)) by lia.
  replace (S (length l) - 1)%nat with (length l) by lia. reflexivity.
Qed.
Lemma last_nth (l : list Z) d : last l d = nth (length l - 1) l d.
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [last length].
  destruct l as [|b l]; [reflexivity|]. rewrite IH. cbn [length].
  replace (S (S (length l)) - 1)%nat with (S (length l)) by lia.
  replace (S (length l) - 1)%nat with (length l) by lia. reflexivity.
Qed.
Lemma upd_nth_len {A} i (f : A -> A) l : length (upd_nth i f l) = length l.
Proof. revert i; induction l as [|x l IH]; intros [|i]; cbn; auto. Qed.
Lemma upd_nth_app_end {A} (f : A -> A) l x : upd_nth (length l) f (l ++ [x]) = l ++ [f x].
Proof. induction l as [|y l IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.
Lemma Forall2_upd {A B} (R : A -> B -> Prop) i f g l1 l2 :
  Forall2 R l1 l2 -> (forall x y, R x y -> R (f x) (g y)) -> Forall2 R (upd_nth i f l1) (upd_nth i g l2).
Proof.
  intros H Hfg; revert i; induction H as [|x y l1 l2 Hxy H IH]; intros [|i]; cbn; constructor; auto.
Qed.
Lemma Forall_upd {A} (P : A -> Prop) i f l : Forall P l -> (forall x, P x -> P (f x)) -> Forall P (upd_nth i f l).
Proof. intros H Hf; revert i; induction H as [|x l Hx H IH]; intros [|i]; cbn; constructor; auto. Qed.
Lemma map_upd {A B} (h : A -> B) i f l : (forall x, h (f x) = h x) -> map h (upd_nth i f l) = map h l.
Proof. intros Hf; revert i; induction l as [|x l IH]; intros [|i]; cbn; rewrite ?Hf, ?IH; reflexivity. Qed.
Lemma Forall2_nth' {A B} (R : A -> B -> Prop) l1 l2 d1 d2 i :
  Forall2 R l1 l2 -> R d1 d2 -> R (nth i l1 d1) (nth i l2 d2).
Proof. intros H Hd; revert i; induction H as [|x y l1 l2 Hxy H IH]; intros [|i]; cbn; auto. Qed.
Lemma Forall_skipn' {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof. intros H; rewrite <- (firstn_skipn n l) in H; apply Forall_app in H; tauto. Qed.
Lemma Forall_firstn' {A} (P : A -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof. intros H; rewrite <- (firstn_skipn n l) in H; apply Forall_app in H; tauto. Qed.
Lemma forallb_seq_Z (P : Z -> bool) lo n :
  forallb (fun k => P (Z.of_nat k)) (seq lo n) = true -> forall z, Z.of_nat lo <= z < Z.of_nat (lo + n) -> P z = true.
Proof.
  intros H z Hz. rewrite forallb_forall in H.
  specialize (H (Z.to_nat z)). rewrite Z2Nat.id in H by lia. apply H. apply in_seq. lia.
Qed.

(** ** 9. Lemmas: the character classes *)

Lemma tolower_lower c : tolower c = lower c.
Proof.
  unfold tolower, lower. destruct ((65 <=? c) && (c <=? 90)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
  assert (H : forallb (fun k => Z.lor (Z.of_nat k) 32 =? Z.of_nat k - 65 + 97) (seq 65 26) = true)
    by (vm_compute; reflexivity).
  apply Z.eqb_eq. exact (forallb_seq_Z (fun z => Z.lor z 32 =? z - 65 + 97) 65 26 H c ltac:(lia)).
Qed.
Lemma lower_eq0 a : lower a = 0 -> a = 0.
Proof. unfold lower; destruct ((65 <=? a) && (a <=? 90)) eqn:E; [|auto]. apply andb_true_iff in E as [E1 _]; apply Z.leb_le in E1; lia. Qed.
Lemma parent_char ch :
  isalnum ch || (ch =? 46) || (ch =? 45) || (ch =? 58) || (ch =? 95) = h_parent_ok ch.
Proof.
  destruct (Z_lt_le_dec ch 0) as [Hn|Hn]; [|destruct (Z_lt_le_dec ch 256) as [Hb|Hb]].
  - unfold isalnum, isalpha, isdigit, h_parent_ok.
    destruct (Z.leb_spec 0 ch); [lia|]. cbn [andb].
    repeat match goal with
           | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
           | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
           end; cbn; first [reflexivity | exfalso; lia].
  - assert (H : forallb (fun k => Bool.eqb (isalnum (Z.of_nat k) || (Z.of_nat k =? 46) || (Z.of_nat k =? 45) ||
                                             (Z.of_nat k =? 58) || (Z.of_nat k =? 95)) (h_parent_ok (Z.of_nat k)))
                        (seq 0 256) = true) by (vm_compute; reflexivity).
    apply Bool.eqb_prop. exact (forallb_seq_Z (fun z => Bool.eqb (isalnum z || (z =? 46) || (z =? 45) || (z =? 58) ||
                                                         (z =? 95)) (h_parent_ok z)) 0 256 H ch ltac:(lia)).
  - unfold isalnum, isalpha, isdigit, h_parent_ok.
    destruct (Z.ltb_spec ch 256); [lia|]. rewrite andb_false_r. cbn [andb].
    repeat match goal with
           | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
           | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
           end; cbn; first [reflexivity | exfalso; lia].
Qed.

(** ** 10. Where the two texts differ in form: each pair proved equal *)

(** strip (H:119-125) and trim (R:50-59). *)
Lemma trim_end_spec l : forall fuel e, (e <= length l)%nat -> (e <= fuel)%nat ->
  firstn (trim_end l e fuel) l = rev (dropwhile blank (rev (firstn e l))).
Proof.
  induction fuel as [|f IH]; intros e He Hf.
  - assert (e = 0%nat) by lia; subst. reflexivity.
  - destruct e as [|e]; [reflexivity|]. cbn [trim_end].
    rewrite (firstn_S_snoc e l) by lia. rewrite rev_app_distr. cbn [rev app dropwhile].
    destruct (blank (nth e l 0)) eqn:Hb.
    + apply IH; lia.
    + cbn [rev]. rewrite rev_involutive. apply firstn_S_snoc; lia.
Qed.
Lemma r_trim_strip s : nulfree s -> r_trim s = h_strip s.
Proof.
  intros H. unfold r_trim, h_strip. rewrite cut_nul_id by exact H.
  rewrite trim_end_spec by lia. rewrite firstn_all. reflexivity.
Qed.

(** The comment loops (H:280-284 against R:65-74). *)
Lemma strip_comment_go suf : forall pre,
  (match first_at (r_comment_at (pre ++ suf)) (length pre) (length suf) with
   | Some i => firstn i (pre ++ suf) | None => pre ++ suf end) = pre ++ h_cut_go (length pre =? 0)%nat (last pre 0) suf.
Proof.
  induction suf as [|q r IH]; intros pre; cbn [first_at length].
  - reflexivity.
  - assert (E1 : nth (length pre) (pre ++ q :: r) 0 = q).
    { rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
    assert (E2 : ((length pre =? 0)%nat || sp_tab (nth (length pre - 1) (pre ++ q :: r) 0)) =
                 ((length pre =? 0)%nat || sp_tab (last pre 0))).
    { destruct pre as [|p0 pre']; [reflexivity|]. rewrite app_nth1 by (cbn; lia).
      rewrite (last_nth (p0 :: pre')). reflexivity. }
    unfold r_comment_at at 1. rewrite E1, E2. cbn [h_cut_go].
    destruct (is_mark q && ((length pre =? 0)%nat || sp_tab (last pre 0))) eqn:Hm; cbv beta iota.
    + rewrite firstn_app, Nat.sub_diag, firstn_all. reflexivity.
    + replace (pre ++ q :: r) with ((pre ++ [q]) ++ r) by (rewrite <- app_assoc; reflexivity).
      replace (S (length pre)) with (length (pre ++ [q])) by (rewrite length_app; cbn; lia).
      rewrite IH. rewrite last_last.
      assert (E3 : (length (pre ++ [q]) =? 0)%nat = false) by (rewrite length_app; cbn [length]; apply Nat.eqb_neq; lia).
      rewrite E3, <- app_assoc. reflexivity.
Qed.
Lemma r_strip_comment_h l : nulfree l -> r_strip_comment l = h_cut_comment l.
Proof.
  intros H. unfold r_strip_comment, h_cut_comment. rewrite cut_nul_id by exact H.
  exact (strip_comment_go l []).
Qed.

(** unquote (R:78-86) and H:207-210. *)
Lemma r_unquote_h v : nulfree v -> r_unquote v = h_unquote v.
Proof.
  intros H. unfold r_unquote, h_unquote. rewrite strlen_id, cut_nul_id by exact H.
  assert (E0 : nth 0 v 0 = hd0 v) by (destruct v; reflexivity).
  rewrite E0, <- last_nth.
  destruct (Nat.leb_spec 2 (length v)) as [Hl|Hl]; cbn [andb]; [|reflexivity].
  assert (Hs : slice 1 (length v - 1) v = removelast (tl v)).
  { unfold slice. destruct v as [|a v]; [cbn in Hl; lia|].
    replace (length (a :: v) - 1 - 1)%nat with (length v - 1)%nat by (cbn [length]; lia).
    cbn [skipn tl]. rewrite removelast_firstn'. reflexivity. }
  rewrite Hs. clear Hs E0.
  destruct (Z.eqb_spec (hd0 v) 34), (Z.eqb_spec (hd0 v) 39), (Z.eqb_spec (last v 0) 34),
           (Z.eqb_spec (last v 0) 39), (Z.eqb_spec (last v 0) (hd0 v)); cbn; try reflexivity; exfalso; lia.
Qed.

(** strcasecmp / strncasecmp (musl) against ieq (H:127-138), for a word of lower-case bytes. *)
Definition wordok (w : list Z) : Prop := Forall (fun x => x <> 0 /\ lower x = x) w.
Lemma wordok_b w : forallb (fun x => negb (x =? 0) && (lower x =? x)) w = true -> wordok w.
Proof.
  induction w as [|x w IH]; cbn; intros H; [constructor|].
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H1 H3].
  constructor; [|apply IH, H2]. split.
  - intros ->. cbn in H1. discriminate.
  - apply Z.eqb_eq, H3.
Qed.
Lemma ieq_cons a l x w : ieq (a :: l) (x :: w) = (lower a =? x) && ieq l w.
Proof.
  unfold ieq; cbn [length ieq_go Nat.eqb].
  destruct (lower a =? x), (length l =? length w)%nat, (ieq_go l w); reflexivity.
Qed.
Lemma lower0 : lower 0 = 0.
Proof. reflexivity. Qed.
Lemma strcasecmp_ieq l : forall w, nulfree l -> wordok w -> (strcasecmp l w =? 0) = ieq l w.
Proof.
  induction l as [|a l IH]; intros [|x w] Hl Hw; cbn [strcasecmp hd0]; rewrite ?tolower_lower, ?lower0.
  - reflexivity.
  - inversion Hw as [|? ? [Hx0 Hxl] Hw']; subst. rewrite Hxl. unfold ieq; cbn [length Nat.eqb andb].
    apply Z.eqb_neq. lia.
  - apply nulfree_cons in Hl as [Ha _]. unfold ieq; cbn [length Nat.eqb andb].
    apply Z.eqb_neq. intros E. apply Ha, lower_eq0. lia.
  - inversion Hw as [|? ? [Hx0 Hxl] Hw']; subst. apply nulfree_cons in Hl as [Ha Hl].
    rewrite Hxl, ieq_cons.
    destruct (Z.eqb_spec a 0) as [|_]; [contradiction|]. destruct (Z.eqb_spec x 0) as [|_]; [contradiction|].
    cbn [negb andb].
    destruct (Z.eqb_spec a x) as [<-|Hax]; cbn [orb].
    + rewrite Hxl, Z.eqb_refl. cbn [andb]. apply IH; auto.
    + destruct (Z.eqb_spec (lower a) x) as [E|E]; cbn [andb].
      * apply IH; auto.
      * apply Z.eqb_neq; lia.
Qed.
Lemma strncasecmp_go_ieq n : forall l x w, nulfree l -> wordok (x :: w) -> length w = n ->
  (strncasecmp_go l (x :: w) n =? 0) = ((S n <=? length l)%nat && ieq (firstn (S n) l) (x :: w)).
Proof.
  induction n as [|n IH]; intros l x w Hl Hw Hn; inversion Hw as [|? ? [Hx0 Hxl] Hw']; subst.
  - destruct w; [|discriminate]. destruct l as [|a l]; cbn [strncasecmp_go hd0]; rewrite ?tolower_lower, ?lower0, Hxl.
    + cbn [length Nat.leb andb]. apply Z.eqb_neq; lia.
    + change (firstn 1 (a :: l)) with [a]. rewrite ieq_cons. cbn [length Nat.leb andb].
      replace (ieq [] []) with true by reflexivity. rewrite andb_true_r.
      destruct (Z.eqb_spec (lower a) x); [apply Z.eqb_eq | apply Z.eqb_neq]; lia.
  - destruct w as [|y w]; [discriminate|]. cbn [length] in Hn; injection Hn as Hn.
    destruct l as [|a l]; cbn [strncasecmp_go hd0].
    + rewrite ?tolower_lower, ?lower0, Hxl. cbn [length Nat.leb andb]. apply Z.eqb_neq; lia.
    + apply nulfree_cons in Hl as [Ha Hl]. rewrite !tolower_lower, Hxl.
      destruct (Z.eqb_spec a 0) as [|_]; [contradiction|]. destruct (Z.eqb_spec x 0) as [|_]; [contradiction|].
      cbn [negb andb].
      change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite ieq_cons.
      replace ((S (S n) <=? length (a :: l))%nat) with ((S n <=? length l)%nat) by reflexivity.
      destruct (Z.eqb_spec a x) as [<-|Hax]; cbn [orb].
      * rewrite Hxl, Z.eqb_refl, andb_true_l. apply IH; auto.
      * destruct (Z.eqb_spec (lower a) x) as [E|E]; cbn [andb].
        -- apply IH; auto.
        -- rewrite andb_false_r. apply Z.eqb_neq; lia.
Qed.
Lemma S_segment_eq : S_segment = 115 :: [101; 103; 109; 101; 110; 116].
Proof. reflexivity. Qed.
Lemma wordok_segment : wordok S_segment.
Proof. apply wordok_b; vm_compute; reflexivity. Qed.
Lemma strncasecmp_segment b : nulfree b ->
  (strncasecmp b S_segment 7 =? 0) = ((7 <=? length b)%nat && ieq (firstn 7 b) S_segment).
Proof.
  intros H. pose proof wordok_segment as Hw. rewrite S_segment_eq in Hw |- *. unfold strncasecmp.
  apply strncasecmp_go_ieq; [exact H | exact Hw | reflexivity].
Qed.
(** The keyword test: R:177-178 against H:168. *)
Lemma kw_cond b : nulfree b ->
  negb (strncasecmp b S_segment 7 =? 0) || negb (sp_tab (nth 7 b 0)) =
  (length b <? 8)%nat || negb (ieq (firstn 7 b) S_segment) || negb (sp_tab (nth 7 b 0)).
Proof.
  intros H. rewrite strncasecmp_segment by exact H.
  destruct (Nat.ltb_spec (length b) 8) as [Hl|Hl].
  - rewrite nth_overflow by lia. replace (negb (sp_tab 0)) with true by reflexivity.
    rewrite !orb_true_r. reflexivity.
  - replace ((7 <=? length b)%nat) with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
Qed.

(** The fold loops (H:141-148 against R:236-238, R:254-256). *)
Lemma r_low_fold_go cap v : forall li, nulfree v -> r_low v li cap = map lower (firstn (cap - S li) v).
Proof.
  induction v as [|q r IH]; intros li H; cbn [r_low].
  - rewrite firstn_nil. reflexivity.
  - apply nulfree_cons in H as [Hq Hr]. destruct (Z.eqb_spec q 0); [contradiction|].
    destruct (Nat.ltb_spec (li + 1) cap) as [Hc|Hc].
    + replace (cap - S li)%nat with (S (cap - S (S li))) by lia. cbn [firstn map]. rewrite IH by exact Hr. reflexivity.
    + replace (cap - S li)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma r_low_fold v cap : nulfree v -> r_low v 0 cap = h_fold v cap.
Proof. intros H. rewrite r_low_fold_go by exact H. reflexivity. Qed.
Lemma h_fold_nulfree v cap : nulfree v -> nulfree (h_fold v cap).
Proof. intros H; apply nulfree_map_lower, nulfree_firstn, H. Qed.
Lemma h_fold_len v cap : (length (h_fold v cap) <= cap - 1)%nat.
Proof. unfold h_fold. rewrite length_map, length_firstn. lia. Qed.

(** reac_role_intent_parse's strcmp chain (RR:110-120) against the word loop (H:214-226). *)
Lemma role_parse_word low : nulfree low -> role_intent_parse low = h_role_word low.
Proof.
  intros H. unfold role_intent_parse, h_role_word. cbn [word_go]. rewrite !len_leqb.
  rewrite !strcmp_eq by (auto; apply nulfree_forallb; vm_compute; reflexivity).
  rewrite !(leqb_sym low). reflexivity.
Qed.

(** parse_bool (R:88-99) against H:238-245. *)
Definition h_ignore_word (v : list Z) : option bool :=
  if ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49)) then Some true
  else if ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48)) then Some false else None.
Lemma parse_bool_h v : nulfree v -> parse_bool v = h_ignore_word v.
Proof.
  intros H. unfold parse_bool, h_ignore_word.
  rewrite !strcasecmp_ieq by (auto; apply wordok_b; vm_compute; reflexivity).
  rewrite !strcmp_eq by (auto; apply nulfree_forallb; vm_compute; reflexivity).
  rewrite !leqb_single. reflexivity.
Qed.

(** The long line's section test: strspn (R:144-146) against the blank loop (H:272-276). *)
Lemma long_lbr l : nulfree l ->
  ((strspn_blank l <? length l)%nat && (nth (strspn_blank l) l 0 =? LBR)) = (hd0 (dropwhile blank l) =? LBR).
Proof.
  intros H. unfold strspn_blank. rewrite cut_nul_id by exact H. clear H.
  induction l as [|a l IH]; cbn [takewhile dropwhile length]; [reflexivity|].
  destruct (blank a); cbn [length nth].
  - rewrite <- IH. reflexivity.
  - reflexivity.
Qed.

(** The lines. *)
Lemma break_nl_len p : (length (snd (break_nl p)) <= length p)%nat.
Proof.
  induction p as [|b p IH]; cbn; [lia|]. destruct (b =? 10); cbn; [lia|].
  destruct (break_nl p) as [l q]; cbn in *; lia.
Qed.
Lemma break_nl_len_cons b p : (length (snd (break_nl (b :: p))) <= length p)%nat.
Proof.
  cbn. destruct (b =? 10); cbn; [lia|]. pose proof (break_nl_len p) as H.
  destruct (break_nl p); cbn in *; lia.
Qed.
Lemma break_nl_nulfree p : nulfree p -> nulfree (fst (break_nl p)) /\ nulfree (snd (break_nl p)).
Proof.
  induction p as [|b p IH]; cbn; intros H; [split; apply nulfree_nil|]. apply nulfree_cons in H as [Hb Hp].
  destruct (b =? 10); cbn; [split; [apply nulfree_nil|exact Hp]|].
  destruct (IH Hp) as [H1 H2]. destruct (break_nl p) as [l q]; cbn in *.
  split; [apply nulfree_cons; auto|exact H2].
Qed.
Lemma lines_go_props fuel : forall p, nulfree p ->
  Forall nulfree (lines_go fuel p) /\ (length (lines_go fuel p) <= length p)%nat.
Proof.
  induction fuel as [|f IH]; intros p H; cbn; [split; [constructor|lia]|].
  destruct p as [|b p']; [split; [constructor|cbn; lia]|].
  pose proof (break_nl_nulfree (b :: p') H) as [H1 H2]. pose proof (break_nl_len_cons b p') as Hl.
  destruct (break_nl (b :: p')) as [l q] eqn:E; cbn in H1, H2, Hl.
  destruct (IH q H2) as [Hf Hlen]. split; [constructor; auto | cbn; lia].
Qed.
Lemma lines_props p : nulfree p -> Forall nulfree (lines p) /\ (length (lines p) <= length p)%nat.
Proof. apply lines_go_props. Qed.

(** printf. *)
Lemma dec_go_nulfree f : forall n acc, nulfree acc -> nulfree (dec_go f n acc).
Proof.
  induction f as [|f IH]; intros n acc H; cbn; [exact H|].
  assert (Hd : nulfree ((48 + n mod 10) :: acc)).
  { apply nulfree_cons; split; [|exact H]. pose proof (Z.mod_pos_bound n 10). lia. }
  destruct (n <? 10); [exact Hd | apply IH, Hd].
Qed.
Lemma dec_nulfree z : nulfree (dec z).
Proof.
  unfold dec. destruct (z <? 0); [apply nulfree_cons; split; [lia|]|]; apply dec_go_nulfree, nulfree_nil.
Qed.
Lemma dec_go_len k : forall f n acc, 0 <= n < 10 ^ (Z.of_nat k + 1) -> (k < f)%nat ->
  (length (dec_go f n acc) <= S k + length acc)%nat.
Proof.
  induction k as [|k IH]; intros f n acc Hn Hf; (destruct f as [|f]; [lia|]); cbn [dec_go].
  - destruct (Z.ltb_spec n 10) as [H|H]; cbn [length]; [lia|]. exfalso. cbn in Hn. lia.
  - destruct (Z.ltb_spec n 10) as [H|H]; cbn [length]; [lia|].
    assert (Hq : 0 <= n / 10 < 10 ^ (Z.of_nat k + 1)).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      replace (Z.of_nat (S k) + 1) with (Z.succ (Z.of_nat k + 1)) in Hn by lia.
      rewrite Z.pow_succ_r in Hn by lia. lia. }
    specialize (IH f (n / 10) ((48 + n mod 10) :: acc) Hq ltac:(lia)). cbn [length] in IH. lia.
Qed.
Lemma dec_len z : 0 <= z <= 65535 -> (length (dec z) <= 5)%nat.
Proof.
  intros H. unfold dec. destruct (Z.ltb_spec z 0); [lia|].
  pose proof (dec_go_len 4 20 z [] ltac:(cbn; lia) ltac:(lia)) as Hd. cbn [length] in Hd. lia.
Qed.
Lemma fmt_nulfree_n n : forall f a, (length f <= n)%nat -> nulfree f -> nulfree (fmt f a).
Proof.
  induction n as [|n IH]; intros f a Hl Hf.
  - destruct f; [apply nulfree_nil | cbn in Hl; lia].
  - destruct f as [|c f1]; [apply nulfree_nil|]. apply nulfree_cons in Hf as [Hc Hf1]. cbn [length] in Hl.
    cbn [fmt]. destruct (negb (c =? 37)); cbv beta iota.
    + apply nulfree_cons; split; [exact Hc | apply IH; auto; lia].
    + destruct f1 as [|c1 f2]; cbv beta iota; [apply nulfree_nil|].
      apply nulfree_cons in Hf1 as [Hc1 Hf2]. cbn [length] in Hl.
      destruct (c1 =? 115); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [apply nulfree_nil|].
        apply nulfree_app; split; [destruct x; cbn; [apply cut_nul_nulfree | apply nulfree_nil] | apply IH; auto; lia]. }
      destruct ((c1 =? 100) || (c1 =? 117)); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [apply nulfree_nil|].
        apply nulfree_app; split; [apply dec_nulfree | apply IH; auto; lia]. }
      destruct (c1 =? 122); cbv beta iota.
      { destruct f2 as [|c2 f3]; cbv beta iota; [apply nulfree_nil|].
        apply nulfree_cons in Hf2 as [_ Hf3]. cbn [length] in Hl.
        destruct (c2 =? 117); cbv beta iota; [|apply nulfree_nil].
        destruct a as [|x a']; cbv beta iota; [apply nulfree_nil|].
        apply nulfree_app; split; [apply dec_nulfree | apply IH; auto; lia]. }
      destruct (c1 =? 46); cbv beta iota; [|apply nulfree_nil].
      destruct f2 as [|d1 [|d2 [|c3 f4]]]; cbv beta iota; try apply nulfree_nil.
      apply nulfree_cons in Hf2 as [_ Hf2]; apply nulfree_cons in Hf2 as [_ Hf2];
        apply nulfree_cons in Hf2 as [_ Hf4].
      cbn [length] in Hl. destruct (isdigit d1 && isdigit d2 && (c3 =? 115)); cbv beta iota; [|apply nulfree_nil].
      destruct a as [|x a']; cbv beta iota; [apply nulfree_nil|].
      apply nulfree_app; split; [apply nulfree_firstn; destruct x; cbn; [apply cut_nul_nulfree | apply nulfree_nil]
                               | apply IH; auto; lia].
Qed.
Lemma fmt_nulfree f a : nulfree f -> nulfree (fmt f a).
Proof. intros H; apply (fmt_nulfree_n (length f)); auto. Qed.
Lemma snprintf_nulfree n f a : nulfree f -> nulfree (snprintf_s n f a).
Proof. intros H; apply nulfree_firstn, fmt_nulfree, H. Qed.
Lemma fmt_addr_line r line : fmt F_addr_line [AS r; AI line] = cut_nul r ++ [58] ++ dec line ++ [58; 32].
Proof. reflexivity. Qed.
Lemma fmt_addr r : fmt F_addr [AS r] = cut_nul r ++ [58; 32].
Proof. reflexivity. Qed.
Lemma fmt_s1 s : fmt F_s [AS s] = cut_nul s.
Proof. change (fmt F_s [AS s]) with (cut_nul s ++ []). apply app_nil_r. Qed.
Lemma snprintf_s1 n s : nulfree s -> (Z.of_nat (length s) < n) -> snprintf_s n F_s [AS s] = s.
Proof. intros H Hl. unfold snprintf_s. rewrite fmt_s1, cut_nul_id by exact H. apply firstn_all2. lia. Qed.
Definition K_rest (v : list Z) : list Z :=
  sb " since 1.0.41: the knock has one content, the control frames, never the stream; remove the line (it says '"%string
  ++ firstn 24 (cut_nul v) ++ sb "')"%string.
Lemma fmt_knock cn v :
  fmt F_knock [AS cn; AS v] = sb "[segment "%string ++ cut_nul cn ++ sb "] knock "%string ++ TNP ++ K_rest v.
Proof. reflexivity. Qed.
Lemma infixb_mid a1 a2 a3 a4 n b : infixb n (a1 ++ a2 ++ a3 ++ a4 ++ n ++ b) = true.
Proof.
  replace (a1 ++ a2 ++ a3 ++ a4 ++ n ++ b) with ((a1 ++ a2 ++ a3 ++ a4) ++ n ++ b) by (rewrite <- !app_assoc; reflexivity).
  apply infixb_app.
Qed.
(** The knock refusal holds "takes no plan" in its first 45 bytes after the address (check_knock_refused). *)
Lemma knock_text P n cn v : (length (cut_nul cn) <= 15)%nat -> (45 <= n)%nat ->
  infixb TNP (P ++ firstn n (fmt F_knock [AS cn; AS v])) = true.
Proof.
  intros Hc Hn. rewrite fmt_knock.
  replace (sb "[segment "%string ++ cut_nul cn ++ sb "] knock "%string ++ TNP ++ K_rest v)
    with ((sb "[segment "%string ++ cut_nul cn ++ sb "] knock "%string ++ TNP) ++ K_rest v)
    by (rewrite <- !app_assoc; reflexivity).
  rewrite firstn_app_le.
  - rewrite <- !app_assoc. apply infixb_mid.
  - rewrite !length_app. change (length (sb "[segment "%string)) with 9%nat.
    change (length (sb "] knock "%string)) with 8%nat. change (length TNP) with 13%nat. lia.
Qed.

(** The VLAN tail: the digit loop with its early exit (H:329-337) against isdigit + strtol (V:42-47). *)
Definition dstep (v d : Z) : Z := v * 10 + (d - 48).
Lemma strtol10_fold s : strtol10 s = fold_left dstep s 0.
Proof. reflexivity. Qed.
Lemma isdigit_range q : isdigit q = true -> 48 <= q <= 57.
Proof. unfold isdigit; intros H; apply andb_true_iff in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia. Qed.
Lemma fold_dstep_ge l : forall v, 0 <= v -> forallb isdigit l = true -> v <= fold_left dstep l v.
Proof.
  induction l as [|d l IH]; intros v Hv H; cbn in *; [lia|]. apply andb_true_iff in H as [Hd Hl].
  apply isdigit_range in Hd. specialize (IH (dstep v d) ltac:(unfold dstep; lia) Hl). unfold dstep in *. lia.
Qed.
Lemma m_digits_spec l : forall vid, 0 <= vid <= 4094 ->
  m_digits l vid = if forallb isdigit l && (fold_left dstep l vid <=? 4094) then Some (fold_left dstep l vid) else None.
Proof.
  induction l as [|q r IH]; intros vid Hv; cbn [m_digits forallb fold_left].
  - destruct (Z.leb_spec vid 4094); [reflexivity | lia].
  - assert (Hd : (q <? 48) || (57 <? q) = negb (isdigit q)).
    { unfold isdigit. destruct (Z.ltb_spec q 48), (Z.ltb_spec 57 q), (Z.leb_spec 48 q), (Z.leb_spec q 57);
        cbn; try reflexivity; lia. }
    rewrite Hd. destruct (isdigit q) eqn:Eq; cbn [negb andb]; [|reflexivity].
    apply isdigit_range in Eq. fold (dstep vid q).
    destruct (Z.ltb_spec 4094 (dstep vid q)) as [Hb|Hb].
    + destruct (forallb isdigit r) eqn:Er; cbn [andb]; [|reflexivity].
      pose proof (fold_dstep_ge r (dstep vid q) ltac:(unfold dstep; lia) Er) as Hge.
      destruct (Z.leb_spec (fold_left dstep r (dstep vid q)) 4094); [lia|reflexivity].
    + apply IH. unfold dstep in *; lia.
Qed.
Lemma last_idx_range c l : forall i acc j, last_idx c l i acc = Some j -> acc = Some j \/ (i <= j < i + length l)%nat.
Proof.
  induction l as [|b l IH]; intros i acc j H; cbn in H; [left; exact H|].
  apply IH in H as [H|H]; [|right; cbn; lia].
  destruct (b =? c); [injection H as <-; right; cbn; lia | left; exact H].
Qed.
Lemma strrchr_lt s c j : strrchr s c = Some j -> (j < length (cut_nul s))%nat.
Proof. unfold strrchr; intros H. apply last_idx_range in H as [H|H]; [discriminate | lia]. Qed.
Lemma forallb_ext' (f g : Z -> bool) l : (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros H; induction l as [|x l IH]; cbn; [reflexivity|]. rewrite H, IH; reflexivity. Qed.
(** reac_declared_vlan_split (V:32-62) against m_split (H:323-350), on a segment name. *)
Lemma split_rel name : nulfree name -> (length name < 16)%nat -> vlan_split name = m_split name.
Proof.
  intros Hn Hl. unfold vlan_split, m_split.
  destruct (strrchr name DOT) as [di|] eqn:Hd; [|reflexivity].
  apply strrchr_lt in Hd. rewrite cut_nul_id in Hd by exact Hn.
  destruct ((di =? 0)%nat || (hd0 (skipn (S di) name) =? 0)) eqn:H0; [reflexivity|].
  apply orb_false_iff in H0 as [H0a _]. apply Nat.eqb_neq in H0a.
  assert (Ht : nulfree (skipn (S di) name)) by (apply nulfree_skipn, Hn).
  rewrite (cut_nul_id _ Ht). rewrite m_digits_spec by lia. rewrite <- strtol10_fold.
  destruct (forallb isdigit (skipn (S di) name)) eqn:Hdig; cbn [negb andb]; [|reflexivity].
  assert (Hv0 : 0 <= strtol10 (skipn (S di) name)) by (rewrite strtol10_fold; apply fold_dstep_ge; auto; lia).
  destruct (Z.leb_spec (strtol10 (skipn (S di) name)) 4094) as [H4|H4].
  - destruct (Z.ltb_spec (strtol10 (skipn (S di) name)) 1) as [H1|H1]; cbn [orb]; [reflexivity|].
    destruct (Z.ltb_spec 4094 (strtol10 (skipn (S di) name))); [lia|]. cbn [orb].
    destruct (Nat.ltb_spec 16 (di + 1)); [lia|]. cbn [orb].
    rewrite strlen_id by exact Hn. destruct (Nat.ltb_spec 16 (length name + 1)); [lia|].
    assert (Hp : nulfree (firstn di name)) by (apply nulfree_firstn, Hn).
    assert (Hpl : length (firstn di name) = di) by (rewrite length_firstn; lia).
    unfold name_ok. rewrite (cut_nul_id _ Hp).
    destruct (firstn di name) as [|x p] eqn:Ep; [cbn in Hpl; lia|].
    rewrite (forallb_ext' _ _ _ parent_char).
    destruct (forallb h_parent_ok (x :: p)); cbn [negb]; [|reflexivity].
    rewrite Z.mod_small by lia. reflexivity.
  - destruct (Z.ltb_spec 4094 (strtol10 (skipn (S di) name))); [|lia]. rewrite orb_true_r. reflexivity.
Qed.

(** The labels and the reading (H:261, R:122). *)
Definition reading_ok (r : list Z) : Prop := nulfree r /\ (1 <= length r <= 95)%nat.
Definition reading_okb (r : list Z) : bool :=
  forallb (fun x => negb (x =? 0)) r && (1 <=? length r)%nat && (length r <=? 95)%nat.
Lemma reading_okb_ok r : reading_okb r = true -> reading_ok r.
Proof.
  unfold reading_okb; intros H. apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  split; [apply nulfree_forallb, H1|]. apply Nat.leb_le in H2; apply Nat.leb_le in H3; lia.
Qed.
Definition rd_of (lab : option (list Z)) : list Z :=
  snprintf_s 96 F_s [AS (match lab with Some l => l | None => S_base end)].
Lemma rd_label_ok lb : 0 <= lb < 256 -> reading_ok (rd_of (label_of lb)).
Proof.
  intros H. apply reading_okb_ok.
  assert (Hall : forallb (fun k => reading_okb (rd_of (label_of (Z.of_nat k)))) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  exact (forallb_seq_Z (fun z => reading_okb (rd_of (label_of z))) 0 256 Hall lb ltac:(lia)).
Qed.
Lemma rd_base : rd_of None = S_base.
Proof. vm_compute; reflexivity. Qed.
Lemma rd_base_ok : reading_ok S_base.
Proof. apply reading_okb_ok; vm_compute; reflexivity. Qed.

(** ** 11. The relation between the reader's state and the model's *)

(** One segment: every field a check reads, equal; the model's bytes only while it is set (the harness does not
    clear them when m_cross drops the model, the reader does: R:313 against H:303). *)
Definition seg_rel (s : rseg) (g : mseg) : Prop :=
  rs_name s = ms_name g /\ rs_role s = ms_role g /\ rs_role_set s = ms_role_set g /\
  rs_ignore s = ms_ignore g /\ rs_ignore_set s = ms_ignore_set g /\
  rs_model_set s = ms_model_set g /\ (ms_model_set g = true -> rs_model s = ms_model g) /\
  rs_role_file s = ms_role_file g /\ rs_ignore_file s = ms_ignore_file g /\ rs_seen_gen s = ms_gen g.
(** What the model's segments always satisfy. *)
Definition seg_ok (g : mseg) : Prop :=
  nulfree (ms_name g) /\ (length (ms_name g) < 16)%nat /\
  (ms_role_set g = true -> hd0 (ms_role_file g) <> 0) /\ (ms_ignore_set g = true -> hd0 (ms_ignore_file g) <> 0).
(** A kept refusal: the reader's text starts with the model's address, and holds "takes no plan" for a knock. *)
Definition kept_rel (t : list Z) (k : list Z * bool) : Prop :=
  nulfree t /\ nulfree (fst k) /\ (exists rest, t = fst k ++ rest) /\ (snd k = true -> infixb TNP t = true).
Definition conf_rel (c : rconf) (m : mconf) : Prop :=
  Forall2 seg_rel (rc_seg c) (mc_seg m) /\ Forall seg_ok (mc_seg m) /\ NoDup (map ms_name (mc_seg m)) /\
  rc_overflow c = mc_overflow m /\ rc_refused c = mc_refused m /\ Forall2 kept_rel (rc_refusal c) (mc_kept m) /\
  rc_reading c = mc_reading m /\ rc_gen c = mc_gen m.
Definition cn_ok (cn : list Z) : Prop := (length (cut_nul cn) <= 15)%nat.

Lemma conf_rel0 : conf_rel rconf0 mconf0.
Proof. unfold conf_rel; cbn; repeat split; constructor. Qed.
Lemma seg_rel_d : seg_rel rseg_d mseg_d.
Proof. unfold seg_rel; cbn; repeat split; intros H; discriminate H. Qed.

Lemma seg_rel_gen s g z : seg_rel s g -> seg_rel (rs_with_gen z s) (ms_with_gen z g).
Proof. unfold seg_rel; cbn; tauto. Qed.
Lemma seg_rel_role s g r f : seg_rel s g -> seg_rel (rs_with_role r f s) (ms_with_role r f g).
Proof. unfold seg_rel; cbn; intuition. Qed.
Lemma seg_rel_model s g md f : seg_rel s g -> seg_rel (rs_with_model md f s) (ms_with_model md g).
Proof. unfold seg_rel; cbn; intuition. Qed.
Lemma seg_rel_ignore s g b f : seg_rel s g -> seg_rel (rs_with_ignore b f s) (ms_with_ignore b f g).
Proof. unfold seg_rel; cbn; intuition. Qed.
Lemma seg_rel_drop_model s g : seg_rel s g -> seg_rel (rs_drop_model s) (ms_drop_model g).
Proof. unfold seg_rel; cbn; intuition discriminate. Qed.
Lemma seg_rel_drop_role s g : seg_rel s g -> seg_rel (rs_drop_role s) (ms_drop_role g).
Proof. unfold seg_rel; cbn; intuition. Qed.
Lemma seg_ok_gen g z : seg_ok g -> seg_ok (ms_with_gen z g).
Proof. unfold seg_ok; cbn; tauto. Qed.
Lemma seg_ok_role g r f : seg_ok g -> hd0 f <> 0 -> seg_ok (ms_with_role r f g).
Proof. unfold seg_ok; cbn; intuition. Qed.
Lemma seg_ok_model g md : seg_ok g -> seg_ok (ms_with_model md g).
Proof. unfold seg_ok; cbn; tauto. Qed.
Lemma seg_ok_ignore g b f : seg_ok g -> hd0 f <> 0 -> seg_ok (ms_with_ignore b f g).
Proof. unfold seg_ok; cbn; intuition. Qed.
Lemma seg_ok_drop_model g : seg_ok g -> seg_ok (ms_drop_model g).
Proof. unfold seg_ok; cbn; tauto. Qed.
Lemma seg_ok_drop_role g : seg_ok g -> seg_ok (ms_drop_role g).
Proof. unfold seg_ok; cbn; intuition discriminate. Qed.

Lemma refuse_proj c l f a :
  rc_seg (refuse c l f a) = rc_seg c /\ rc_overflow (refuse c l f a) = rc_overflow c /\
  rc_reading (refuse c l f a) = rc_reading c /\ rc_gen (refuse c l f a) = rc_gen c.
Proof.
  unfold refuse; cbv zeta. destruct (8 <=? _); [repeat split; reflexivity|].
  destruct (_ || _); repeat split; reflexivity.
Qed.
Lemma m_header_reading m l n : mc_reading (fst (m_header m l n)) = mc_reading m.
Proof.
  unfold m_header. cbv zeta. destruct (memchr l RBR) as [ci|]; [|reflexivity].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [m_find ?a ?b] => destruct (m_find a b)
         end; reflexivity.
Qed.
Lemma m_key_reading m g l n : mc_reading (m_key m g l n) = mc_reading m.
Proof.
  unfold m_key. cbv zeta. destruct (memchr l EQ); [|reflexivity]. destruct g; [|reflexivity].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [h_role_word ?a] => destruct (h_role_word a)
         | |- context [cat_row ?a] => destruct (cat_row a)
         end; reflexivity.
Qed.
Lemma m_line_reading m cur n l : mc_reading (fst (m_line (m, cur) n l)) = mc_reading m.
Proof.
  unfold m_line. destruct (512 <=? length l)%nat; [reflexivity|].
  destruct (h_strip (h_cut_comment l)) as [|b s]; [reflexivity|].
  destruct (b =? LBR); [apply m_header_reading | apply m_key_reading].
Qed.

(** The address both texts print: [<file>:<line>: ] or [<file>: ] (R:39-40, H:104-107). *)
Definition addr_text (r : list Z) (line : Z) : list Z :=
  if 0 <? line then r ++ [58] ++ dec line ++ [58; 32] else r ++ [58; 32].
Lemma addr_eq c line : reading_ok (rc_reading c) ->
  fmt (r_addr_fmt line) (r_addr_args c line) = addr_text (rc_reading c) line.
Proof.
  intros [Hn Hl].
  assert (Hw : r_where c = rc_reading c).
  { unfold r_where. rewrite hd0_eq0 by exact Hn. destruct (rc_reading c); [cbn in Hl; lia | reflexivity]. }
  unfold r_addr_fmt, r_addr_args, addr_text. rewrite Hw.
  destruct (0 <? line); [rewrite fmt_addr_line | rewrite fmt_addr]; rewrite cut_nul_id by exact Hn; reflexivity.
Qed.
Lemma addr_text_ok r line : reading_ok r -> 0 <= line <= 65535 ->
  nulfree (addr_text r line) /\ (length (addr_text r line) <= 103)%nat.
Proof.
  intros [Hn Hl] Hline. unfold addr_text. destruct (0 <? line).
  - split.
    + apply nulfree_app; split; [exact Hn|]. apply nulfree_app; split; [apply nulfree_forallb; reflexivity|].
      apply nulfree_app; split; [apply dec_nulfree | apply nulfree_forallb; reflexivity].
    + rewrite !length_app. pose proof (dec_len line Hline). cbn [length]. lia.
  - split.
    + apply nulfree_app; split; [exact Hn | apply nulfree_forallb; reflexivity].
    + rewrite length_app. cbn [length]. lia.
Qed.
Lemma m_addr_eq r line : reading_ok r -> 0 <= line <= 65535 ->
  (if 0 <? line then snprintf_s 112 F_addr_line [AS r; AI line] else snprintf_s 112 F_addr [AS r]) =
  addr_text r line.
Proof.
  intros Hr Hline. pose proof (addr_text_ok r line Hr Hline) as [_ Hlen]. destruct Hr as [Hn _].
  unfold snprintf_s. revert Hlen. unfold addr_text. destruct (0 <? line); intros Hlen;
    [rewrite fmt_addr_line | rewrite fmt_addr]; rewrite cut_nul_id by exact Hn;
    apply firstn_all2; change (Z.to_nat (112 - 1)) with 111%nat; lia.
Qed.

(** refuse (R:30-48) and m_refuse (H:101-111) keep the relation: the address fits the slot (k < 200, so R:41 never
    drops a refusal the model keeps), and the model's 112-byte copy of the address is the reader's prefix. *)
Lemma refuse_rel c m line f a knock :
  conf_rel c m -> reading_ok (mc_reading m) -> 0 <= line <= 65535 -> nulfree f ->
  (knock = true -> f = F_knock /\ exists cn v, a = [AS cn; AS v] /\ (length (cut_nul cn) <= 15)%nat) ->
  conf_rel (refuse c line f a) (m_refuse m line knock).
Proof.
  intros Hc Hr Hline Hf Hk. destruct Hc as (Hs & Hok & Hnd & Hov & Href & Hkept & Hrd & Hgen).
  pose proof (Forall2_length Hkept) as Hlen.
  assert (Hr' : reading_ok (rc_reading c)) by (rewrite Hrd; exact Hr).
  pose proof (addr_text_ok (rc_reading c) line Hr' Hline) as [Hpn Hpl].
  unfold m_refuse. rewrite (m_addr_eq (mc_reading m) line Hr Hline), <- Hrd.
  unfold refuse, snprintf_r, snprintf_s. cbv zeta. rewrite (addr_eq c line Hr').
  set (P := addr_text (rc_reading c) line) in *.
  destruct (Z.leb_spec 8 (Z.of_nat (length (rc_refusal c)))) as [H8|H8].
  - destruct (Z.ltb_spec (Z.of_nat (length (mc_kept m))) 8); [lia|].
    unfold conf_rel; cbn [rc_seg rc_overflow rc_refused rc_refusal rc_reading rc_gen mc_seg mc_overflow mc_refused
                          mc_kept mc_reading mc_gen].
    refine (conj Hs (conj Hok (conj Hnd (conj Hov (conj _ (conj Hkept (conj eq_refl Hgen))))))). congruence.
  - destruct (Z.ltb_spec (Z.of_nat (length (mc_kept m))) 8); [|lia].
    destruct (Z.ltb_spec (Z.of_nat (length P)) 0); [lia|].
    destruct (Z.leb_spec 200 (Z.of_nat (length P))); [lia|]. cbn [orb].
    rewrite (firstn_all2 (n := Z.to_nat (200 - 1)) P) by (change (Z.to_nat (200 - 1)) with 199%nat; lia).
    unfold conf_rel; cbn [rc_seg rc_overflow rc_refused rc_refusal rc_reading rc_gen mc_seg mc_overflow mc_refused
                          mc_kept mc_reading mc_gen].
    refine (conj Hs (conj Hok (conj Hnd (conj Hov (conj _ (conj _ (conj eq_refl Hgen))))))); [congruence|].
    apply Forall2_app; [exact Hkept|]. constructor; [|constructor].
    unfold kept_rel; cbn [fst snd]. split; [|split; [exact Hpn|split; [eexists; reflexivity|]]].
    + apply nulfree_app; split; [exact Hpn | apply nulfree_firstn, fmt_nulfree, Hf].
    + intros Hkn. destruct (Hk Hkn) as [-> (cn & v & -> & Hcn)]. apply knock_text; [exact Hcn | lia].
Qed.

Ltac refuse_ok :=
  apply refuse_rel; [assumption | assumption | lia | apply nulfree_forallb; vm_compute; reflexivity
                    | intros Hkk; discriminate Hkk].

Lemma upd_rel c m i fr fm :
  conf_rel c m -> (forall s g, seg_rel s g -> seg_rel (fr s) (fm g)) -> (forall g, seg_ok g -> seg_ok (fm g)) ->
  (forall g, ms_name (fm g) = ms_name g) -> conf_rel (r_upd c i fr) (m_upd m i fm).
Proof.
  intros (Hs & Hok & Hnd & Hov & Href & Hkept & Hrd & Hgen) H1 H2 H3.
  unfold r_upd, m_upd, r_set_segs, m_set_segs, conf_rel;
    cbn [rc_seg rc_overflow rc_refused rc_refusal rc_reading rc_gen mc_seg mc_overflow mc_refused mc_kept mc_reading mc_gen].
  refine (conj (Forall2_upd _ _ _ _ _ _ Hs H1) (conj (Forall_upd _ _ _ _ Hok H2)
            (conj _ (conj Hov (conj Href (conj Hkept (conj Hrd Hgen))))))).
  rewrite map_upd by exact H3. exact Hnd.
Qed.
Lemma NoDup_snoc {A} (l : list A) x : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  induction l as [|y l IH]; intros Hnd Hn; cbn; [constructor; [intros []|constructor]|].
  inversion Hnd as [|? ? Hy Hnd']; subst. constructor.
  - rewrite in_app_iff. intros [H|[H|[]]]; [exact (Hy H) | apply Hn; left; congruence].
  - apply IH; [exact Hnd' | intros H; apply Hn; right; exact H].
Qed.
Lemma append_rel c m s g :
  conf_rel c m -> seg_rel s g -> seg_ok g -> ~ In (ms_name g) (map ms_name (mc_seg m)) ->
  conf_rel (r_set_segs c (rc_seg c ++ [s])) (m_set_segs m (mc_seg m ++ [g])).
Proof.
  intros (Hs & Hok & Hnd & Hov & Href & Hkept & Hrd & Hgen) H1 H2 H3.
  unfold r_set_segs, m_set_segs, conf_rel;
    cbn [rc_seg rc_overflow rc_refused rc_refusal rc_reading rc_gen mc_seg mc_overflow mc_refused mc_kept mc_reading mc_gen].
  refine (conj _ (conj _ (conj _ (conj Hov (conj Href (conj Hkept (conj Hrd Hgen))))))).
  - apply Forall2_app; [exact Hs | constructor; [exact H1 | constructor]].
  - apply Forall_app; split; [exact Hok | constructor; [exact H2 | constructor]].
  - rewrite map_app. apply NoDup_snoc; assumption.
Qed.

(** seg_get / reac_segconf_find's strcmp scan against m_find's strlen + memcmp. *)
Lemma find_rel rs ms name i : Forall2 seg_rel rs ms -> Forall seg_ok ms -> nulfree name ->
  r_find_go rs name i = m_find_go ms name i.
Proof.
  intros H; revert i; induction H as [|s g rs ms Hsg H IH]; intros i Hok Hn; cbn; [reflexivity|].
  inversion Hok as [|? ? Hg Hok']; subst. destruct Hsg as [Hname _]. destruct Hg as [Hgn _].
  rewrite Hname, strcmp_eq by auto. rewrite strlen_id by auto. rewrite len_leqb.
  destruct (leqb (ms_name g) name); [reflexivity|]. apply IH; auto.
Qed.
Lemma m_find_go_none ms name i : Forall seg_ok ms -> nulfree name -> m_find_go ms name i = None ->
  ~ In name (map ms_name ms).
Proof.
  revert i; induction ms as [|g ms IH]; intros i Hok Hn H; cbn in *; [auto|].
  inversion Hok as [|? ? [Hgn _] Hok']; subst.
  rewrite strlen_id in H by auto. rewrite len_leqb in H.
  destruct (leqb (ms_name g) name) eqn:E; [discriminate|].
  intros [E'|Hin]; [rewrite E', leqb_refl in E; discriminate|]. eapply IH; eauto.
Qed.
Lemma m_find_go_nth ms i k : Forall seg_ok ms -> NoDup (map ms_name ms) -> (i < length ms)%nat ->
  m_find_go ms (ms_name (nth i ms mseg_d)) k = Some (k + i)%nat.
Proof.
  revert i k; induction ms as [|g ms IH]; intros i k Hok Hnd Hi; cbn in Hi; [lia|].
  inversion Hok as [|? ? [Hgn _] Hok']; subst. inversion Hnd as [|? ? Hnin Hnd']; subst.
  cbn [m_find_go]. rewrite strlen_id by auto. rewrite len_leqb. destruct i as [|i].
  - cbn [nth]. rewrite leqb_refl. f_equal; lia.
  - cbn [nth]. destruct (leqb (ms_name g) (ms_name (nth i ms mseg_d))) eqn:E.
    + apply leqb_eq in E. exfalso; apply Hnin. rewrite E. apply in_map, nth_In; lia.
    + rewrite IH by (auto; lia). f_equal; lia.
Qed.

Lemma cn_ok_snprintf16 a : cn_ok (snprintf_s 16 F_s a).
Proof.
  unfold cn_ok, snprintf_s. pose proof (cut_nul_len (firstn (Z.to_nat (16 - 1)) (fmt F_s a))) as H.
  rewrite length_firstn in H. change (Z.to_nat (16 - 1)) with 15%nat in *. lia.
Qed.
Lemma rd_file r : reading_ok r -> snprintf_s 96 F_s [AS r] = r /\ hd0 r <> 0.
Proof.
  intros [Hn Hl]. split; [apply snprintf_s1; [exact Hn | lia]|].
  destruct r as [|x r]; [cbn in Hl; lia|]. apply nulfree_cons in Hn as [Hx _]. exact Hx.
Qed.

(** ** 12. One line, one file, the cross rules, the run *)

(** The header branch (R:159-213 against H:159-194). *)
Lemma header_rel c m cn lineno line :
  conf_rel c m -> reading_ok (mc_reading m) -> nulfree line -> 1 <= lineno <= 65535 ->
  let '(c', cur', cn') := r_header c cn lineno line in
  conf_rel c' (fst (m_header m line lineno)) /\ cur' = snd (m_header m line lineno) /\ (cn_ok cn -> cn_ok cn').
Proof.
  intros Hc Hr Hn Hline. unfold r_header, m_header. cbv zeta.
  rewrite strchr_memchr by (auto; discriminate).
  destruct (memchr line RBR) as [ci|] eqn:Hci.
  2: { cbn [fst snd]. split; [refuse_ok|]. split; [reflexivity | auto]. }
  pose proof (memchr_lt _ _ _ Hci) as Hlt.
  rewrite (nth_after_close line ci Hn Hlt).
  destruct (S ci =? length line)%nat eqn:Hend; cbn [negb].
  2: { cbn [fst snd]. split; [refuse_ok|]. split; [reflexivity | auto]. }
  assert (Hbn : nulfree (slice 1 ci line)) by (apply nulfree_slice, Hn).
  rewrite (r_trim_strip _ Hbn).
  remember (h_strip (slice 1 ci line)) as b eqn:Eb.
  assert (Hb : nulfree b) by (rewrite Eb; apply nulfree_h_strip, Hbn).
  rewrite (kw_cond b Hb).
  destruct ((length b <? 8)%nat || negb (ieq (firstn 7 b) S_segment) || negb (sp_tab (nth 7 b 0))) eqn:Hkw.
  { cbn [fst snd]. split; [refuse_ok|]. split; [reflexivity | auto]. }
  assert (Hnn : nulfree (skipn 7 b)) by (apply nulfree_skipn, Hb).
  rewrite (r_trim_strip _ Hnn).
  remember (h_strip (skipn 7 b)) as nm eqn:Enm.
  assert (Hnm : nulfree nm) by (rewrite Enm; apply nulfree_h_strip, Hnn).
  rewrite (strlen_id nm Hnm), (hd0_eq0 nm Hnm).
  destruct nm as [|x nm'].
  { cbv beta iota. cbn [length Nat.eqb orb fst snd]. split; [refuse_ok|]. split; [reflexivity | auto]. }
  cbv beta iota. replace ((length (x :: nm') =? 0)%nat) with false by reflexivity. cbn [orb].
  destruct (16 <=? length (x :: nm'))%nat eqn:H16.
  { cbn [fst snd]. split; [refuse_ok|]. split; [reflexivity | auto]. }
  apply Nat.leb_gt in H16.
  pose proof Hc as (Hs & Hok & Hnd & Hov & Href & Hkept & Hrd & Hgen).
  unfold seg_get, m_find. rewrite (find_rel (rc_seg c) (mc_seg m) (x :: nm') 0 Hs Hok Hnm).
  destruct (m_find_go (mc_seg m) (x :: nm') 0) as [i|] eqn:Hf.
  - cbv beta iota. cbn [negb andb].
    pose proof (Forall2_nth' seg_rel _ _ rseg_d mseg_d i Hs seg_rel_d) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hgi).
    rewrite Hgi, Hgen.
    destruct (ms_gen (nth i (mc_seg m) mseg_d) =? mc_gen m) eqn:Hg; cbn [fst snd].
    + split; [|split; [reflexivity | intros _; apply cn_ok_snprintf16]].
      destruct (refuse_proj c lineno F_twice [AS (x :: nm')]) as (_ & _ & _ & Hg2). rewrite Hg2, Hgen.
      apply upd_rel; [refuse_ok | intros s g; apply seg_rel_gen | intros g; apply seg_ok_gen | reflexivity].
    + split; [|split; [reflexivity | intros _; apply cn_ok_snprintf16]]. rewrite Hgen.
      apply upd_rel; [exact Hc | intros s g; apply seg_rel_gen | intros g; apply seg_ok_gen | reflexivity].
  - rewrite <- (Forall2_length Hs).
    destruct (32 <=? length (rc_seg c))%nat eqn:H32; cbv beta iota; cbn [fst snd].
    + split; [|split; [reflexivity | auto]].
      apply refuse_rel; [| exact Hr | lia | apply nulfree_forallb; vm_compute; reflexivity | intros Hkk; discriminate Hkk].
      unfold conf_rel; cbn [rc_seg rc_overflow rc_refused rc_refusal rc_reading rc_gen mc_seg mc_overflow mc_refused
                            mc_kept mc_reading mc_gen].
      repeat split; auto. congruence.
    + split; [|split; [reflexivity | intros _; apply cn_ok_snprintf16]].
      rewrite (snprintf_s1 16 (x :: nm') Hnm) by lia. cbn [negb andb].
      assert (Eu : forall f, r_upd (r_set_segs c (rc_seg c ++ [rseg0 (x :: nm')])) (length (rc_seg c)) f =
                             r_set_segs c (rc_seg c ++ [f (rseg0 (x :: nm'))])).
      { intros f. unfold r_upd, r_set_segs. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
        rewrite upd_nth_app_end. reflexivity. }
      rewrite Eu.
      replace (rc_gen (r_set_segs c (rc_seg c ++ [rseg0 (x :: nm')]))) with (mc_gen m)
        by (rewrite <- Hgen; reflexivity).
      apply append_rel; [exact Hc | | | eapply m_find_go_none; eauto].
      * unfold seg_rel; cbn; repeat split; intros Hx; discriminate Hx.
      * cbn [length] in H16. unfold seg_ok; cbn; repeat split; [exact Hnm | lia | |]; intros Hx; discriminate Hx.
Qed.

(** The key branch (R:215-293 against H:197-257). *)
Lemma key_rel c m cur cn lineno line :
  conf_rel c m -> reading_ok (mc_reading m) -> nulfree line -> 1 <= lineno <= 65535 -> cn_ok cn ->
  let '(c', cur', cn') := r_key c cur cn lineno line in
  conf_rel c' (m_key m cur line lineno) /\ cur' = cur /\ cn' = cn.
Proof.
  intros Hc Hr Hn Hline Hcn. unfold r_key, m_key. cbv zeta.
  rewrite strchr_memchr by (auto; discriminate).
  destruct (memchr line EQ) as [ei|] eqn:Hei.
  2: { split; [refuse_ok|]. split; reflexivity. }
  assert (Hk : nulfree (firstn ei line)) by (apply nulfree_firstn, Hn).
  assert (Hv0 : nulfree (skipn (S ei) line)) by (apply nulfree_skipn, Hn).
  rewrite (r_trim_strip _ Hk), (r_trim_strip _ Hv0).
  assert (Hv1 : nulfree (h_strip (skipn (S ei) line))) by (apply nulfree_h_strip, Hv0).
  rewrite (r_unquote_h _ Hv1).
  remember (h_strip (firstn ei line)) as k eqn:Ek.
  remember (h_unquote (h_strip (skipn (S ei) line))) as v eqn:Ev.
  assert (Hkn : nulfree k) by (rewrite Ek; apply nulfree_h_strip, Hk).
  assert (Hvn : nulfree v) by (rewrite Ev; apply nulfree_h_unquote, Hv1).
  destruct cur as [gi|].
  2: { split; [refuse_ok|]. split; reflexivity. }
  pose proof Hc as (Hs & Hok & Hnd & Hov & Href & Hkept & Hrd & Hgen).
  destruct (rd_file _ Hr) as [Hrf Hrh0].
  rewrite Hrd, Hrf.
  rewrite !(strcasecmp_ieq k) by (auto; apply wordok_b; vm_compute; reflexivity).
  destruct (ieq k S_role) eqn:Hrole.
  { rewrite (r_low_fold v 64 Hvn), (role_parse_word _ (h_fold_nulfree v 64 Hvn)).
    destruct (h_role_word (h_fold v 64)) as [r|] eqn:Hw.
    - split; [|split; reflexivity].
      apply upd_rel; [exact Hc | intros s g; apply seg_rel_role | intros g Hg; apply seg_ok_role; assumption
                     | reflexivity].
    - split; [refuse_ok|]. split; reflexivity. }
  destruct (ieq k S_model) eqn:Hmodel.
  { rewrite (r_low_fold v 24 Hvn). unfold by_token. rewrite (cut_nul_id _ (h_fold_nulfree v 24 Hvn)).
    destruct (cat_row (h_fold v 24)) eqn:Hcat.
    - split; [|split; reflexivity].
      rewrite (snprintf_s1 24 (h_fold v 24) (h_fold_nulfree v 24 Hvn)) by (pose proof (h_fold_len v 24); lia).
      apply upd_rel; [exact Hc | intros s g; apply seg_rel_model | intros g; apply seg_ok_model | reflexivity].
    - split; [refuse_ok|]. split; reflexivity. }
  destruct (ieq k S_ignore) eqn:Hign.
  { rewrite (parse_bool_h v Hvn). unfold h_ignore_word.
    destruct (ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49))) eqn:Hy.
    - split; [|split; reflexivity].
      apply upd_rel; [exact Hc | intros s g; apply seg_rel_ignore | intros g Hg; apply seg_ok_ignore; assumption
                     | reflexivity].
    - destruct (ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48))) eqn:Hno.
      + split; [|split; reflexivity].
        apply upd_rel; [exact Hc | intros s g; apply seg_rel_ignore | intros g Hg; apply seg_ok_ignore; assumption
                       | reflexivity].
      + split; [refuse_ok|]. split; reflexivity. }
  destruct (ieq k S_knock) eqn:Hknock.
  { split; [|split; reflexivity].
    apply refuse_rel; [exact Hc | exact Hr | lia | apply nulfree_forallb; vm_compute; reflexivity |].
    intros _. split; [reflexivity | exists cn, v; split; [reflexivity | exact Hcn]]. }
  split; [refuse_ok|]. split; reflexivity.
Qed.

(** One line (R:131-158 against H:266-291). *)
Lemma line_rel c m cur cn lineno l :
  conf_rel c m -> reading_ok (mc_reading m) -> nulfree l -> 1 <= lineno <= 65535 -> cn_ok cn ->
  let '(c', cur', cn') := r_line c cur cn lineno l in
  conf_rel c' (fst (m_line (m, cur) lineno l)) /\ cur' = snd (m_line (m, cur) lineno l) /\ cn_ok cn'.
Proof.
  intros Hc Hr Hn Hline Hcn. unfold r_line, m_line. cbv zeta.
  destruct (512 <=? length l)%nat eqn:Hlong.
  - rewrite (long_lbr l Hn). cbn [fst snd]. split; [refuse_ok|]. split; [reflexivity | exact Hcn].
  - rewrite (r_strip_comment_h l Hn).
    assert (Hcm : nulfree (h_cut_comment l)) by (apply nulfree_h_cut, Hn).
    rewrite (r_trim_strip _ Hcm).
    assert (Hs : nulfree (h_strip (h_cut_comment l))) by (apply nulfree_h_strip, Hcm).
    rewrite (hd0_eq0 _ Hs).
    revert Hs. destruct (h_strip (h_cut_comment l)) as [|b s]; intros Hs; cbv beta iota.
    + cbn [fst snd]. split; [exact Hc|]. split; [reflexivity|exact Hcn].
    + cbn [hd0]. destruct (b =? LBR) eqn:Hb.
      * pose proof (header_rel c m cn lineno (b :: s) Hc Hr Hs Hline) as H.
        destruct (r_header c cn lineno (b :: s)) as [[c' cur'] cn'].
        destruct H as (H1 & H2 & H3). split; [exact H1 | split; [exact H2 | exact (H3 Hcn)]].
      * pose proof (key_rel c m cur cn lineno (b :: s) Hc Hr Hs Hline Hcn) as H.
        destruct (r_key c cur cn lineno (b :: s)) as [[c' cur'] cn'].
        destruct H as (H1 & H2 & H3). subst cur' cn'. cbn [fst snd].
        split; [exact H1 | split; [reflexivity | exact Hcn]].
Qed.

Lemma lines_rel ls : forall c m cur cn n,
  conf_rel c m -> reading_ok (mc_reading m) -> Forall nulfree ls -> 0 <= n -> n + Z.of_nat (length ls) <= 65535 ->
  cn_ok cn ->
  let '(c', cur', cn') := r_lines (c, cur, cn) n ls in
  conf_rel c' (fst (m_lines (m, cur) n ls)) /\ cur' = snd (m_lines (m, cur) n ls) /\
  mc_reading (fst (m_lines (m, cur) n ls)) = mc_reading m.
Proof.
  induction ls as [|l ls IH]; intros c m cur cn n Hc Hr Hf Hn Hlen Hcn; cbn [r_lines m_lines].
  - split; [exact Hc|]. split; reflexivity.
  - inversion Hf as [|? ? Hl Hf']; subst. cbn [length] in Hlen.
    pose proof (line_rel c m cur cn (n + 1) l Hc Hr Hl ltac:(lia) Hcn) as H.
    pose proof (m_line_reading m cur (n + 1) l) as Hrd.
    revert H Hrd.
    destruct (r_line c cur cn (n + 1) l) as [[c1 cur1] cn1].
    destruct (m_line (m, cur) (n + 1) l) as [m1 curm1]. cbn [fst snd]. intros (H1 & H2 & H3) Hrd. subst cur1.
    pose proof (IH c1 m1 curm1 cn1 (n + 1) H1 ltac:(rewrite Hrd; exact Hr) Hf' ltac:(lia) ltac:(lia) H3) as HI.
    revert HI. destruct (r_lines (c1, curm1, cn1) (n + 1) ls) as [[c2 cur2] cn2].
    intros (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|]. rewrite I3, Hrd. reflexivity.
Qed.

(** One file: reac_segconf_parse_file (R:120-296) against m_file (H:259-293). *)
Lemma file_rel c m text lr lm :
  conf_rel c m -> nulfree text -> Z.of_nat (length text) <= 65535 ->
  (match lr with Some l => l | None => S_base end) = (match lm with Some l => l | None => S_base end) ->
  reading_ok (rd_of lm) ->
  conf_rel (fst (r_parse_file c text lr)) (m_file m text lm) /\
  snd (r_parse_file c text lr) = Z.of_nat (length (mc_seg (m_file m text lm))) /\
  mc_reading (m_file m text lm) = rd_of lm.
Proof.
  intros Hc Hn Hlen Hlab Hrd. unfold r_parse_file, m_file. cbv zeta.
  rewrite Hlab. fold (rd_of lm).
  assert (Hc1 : conf_rel (RConf (rc_seg c) (rc_refusal c) (rc_refused c) (rc_overflow c) (rd_of lm) (rc_gen c + 1))
                         (MConf (mc_seg m) (mc_overflow m) (mc_refused m) (mc_kept m) (mc_gen m + 1) (rd_of lm))).
  { destruct Hc as (Hs & Hok & Hnd & Hov & Href & Hkept & Hrd' & Hgen). unfold conf_rel; cbn.
    repeat split; auto. congruence. }
  pose proof (lines_props text Hn) as [Hlf Hll].
  pose proof (lines_rel (lines text) _ _ None [] 0 Hc1 Hrd Hlf ltac:(lia) ltac:(lia)
                        ltac:(unfold cn_ok; cbn; lia)) as H.
  revert H. destruct (r_lines _ 0 (lines text)) as [[c2 cur2] cn2]. intros (H1 & H2 & H3).
  cbn [fst snd]. split; [exact H1|]. split; [|exact H3].
  f_equal. destruct H1 as [Hs2 _]. apply (Forall2_length Hs2).
Qed.

(** The cross rules: cross_check (R:303-325) against m_cross (H:296-310). *)
Lemma m_cross_seg_reading m i : mc_reading (m_cross_seg m i) = mc_reading m.
Proof.
  unfold m_cross_seg. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Lemma m_cross_seg_len m i : length (mc_seg (m_cross_seg m i)) = length (mc_seg m).
Proof.
  unfold m_cross_seg. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    try reflexivity; unfold m_upd, m_set_segs, m_refuse; cbn [mc_seg]; apply upd_nth_len.
Qed.
Lemma m_cross_len m : length (mc_seg (m_cross m)) = length (mc_seg m).
Proof.
  unfold m_cross. generalize (seq 0 (length (mc_seg m))). intros is. revert m.
  induction is as [|i is IH]; intros m; cbn [fold_left]; [reflexivity|]. rewrite IH. apply m_cross_seg_len.
Qed.
Lemma cross_seg_rel c m i : conf_rel c m -> mc_reading m = S_base -> conf_rel (r_cross_seg c i) (m_cross_seg m i).
Proof.
  intros Hc Hrd. pose proof Hc as (Hs & _).
  assert (Hr : reading_ok (mc_reading m)) by (rewrite Hrd; exact rd_base_ok).
  unfold r_cross_seg, m_cross_seg. cbv zeta.
  pose proof (Forall2_nth' seg_rel _ _ rseg_d mseg_d i Hs seg_rel_d) as (H1 & H2 & H3 & _ & _ & H6 & _).
  rewrite H2, H3, H6.
  destruct (ms_model_set (nth i (mc_seg m) mseg_d) &&
            negb (ms_role_set (nth i (mc_seg m) mseg_d) && (ms_role (nth i (mc_seg m) mseg_d) =? 4))).
  - apply upd_rel; [refuse_ok | intros s g; apply seg_rel_drop_model | intros g; apply seg_ok_drop_model
                   | reflexivity].
  - destruct (ms_role_set (nth i (mc_seg m) mseg_d) && (ms_role (nth i (mc_seg m) mseg_d) =? 4) &&
              negb (ms_model_set (nth i (mc_seg m) mseg_d))).
    + apply upd_rel; [refuse_ok | intros s g; apply seg_rel_drop_role | intros g; apply seg_ok_drop_role
                     | reflexivity].
    + exact Hc.
Qed.
Lemma cross_rel c m : conf_rel c m -> mc_reading m = S_base -> conf_rel (cross_check c) (m_cross m).
Proof.
  intros Hc Hrd. unfold cross_check, m_cross.
  pose proof Hc as (Hs & _). rewrite (Forall2_length Hs).
  generalize (seq 0 (length (mc_seg m))) as is. intros is. revert c m Hc Hrd Hs.
  induction is as [|i is IH]; intros c m Hc Hrd Hs; cbn [fold_left]; [exact Hc|].
  pose proof (cross_seg_rel c m i Hc Hrd) as Hc'.
  apply IH; [exact Hc' | rewrite m_cross_seg_reading; exact Hrd | destruct Hc' as [Hs' _]; exact Hs'].
Qed.

(** The file loop of LLVMFuzzerTestOneInput (H:597-620). *)
Definition file_ok (f : file) : Prop :=
  nulfree (f_text f) /\ Z.of_nat (length (f_text f)) <= 65535 /\ 0 <= f_lb f < 256.
Lemma run_rel fs : forall c m ret, conf_rel c m -> Forall file_ok fs ->
  let '(c', m', ret') := run_files fs c m ret in conf_rel c' m' /\ ret' = ret.
Proof.
  induction fs as [|f fs IH]; intros c m ret Hc Hf; [split; [exact Hc|reflexivity]|].
  inversion Hf as [|? ? (Hn & Hl & Hlb) Hf']; subst.
  destruct fs as [|f2 fs'].
  - cbn [run_files]. unfold r_parse.
    pose proof (file_rel c m (f_text f) (Some S_base) None Hc Hn Hl eq_refl
                         ltac:(rewrite rd_base; exact rd_base_ok)) as H.
    revert H. destruct (r_parse_file c (f_text f) (Some S_base)) as [c1 n]. cbn [fst snd]. intros (H1 & H2 & H3).
    split; [apply cross_rel; [exact H1 | rewrite H3; exact rd_base] |].
    rewrite H2, m_cross_len, Z.eqb_refl, andb_true_r. reflexivity.
  - cbn [run_files].
    pose proof (file_rel c m (f_text f) (label_of (f_lb f)) (label_of (f_lb f)) Hc Hn Hl eq_refl
                         (rd_label_ok _ Hlb)) as H.
    revert H. destruct (r_parse_file c (f_text f) (label_of (f_lb f))) as [c1 n]. cbn [fst snd].
    intros (H1 & H2 & _). rewrite H2, Z.eqb_refl, andb_true_r. apply IH; auto.
Qed.

(** ** 13. The checks (H:622-665) *)

Lemma forallb2_names rs ms : Forall2 seg_rel rs ms ->
  forallb2 (fun s g => strcmp (rs_name s) (ms_name g) =? 0) rs ms = true.
Proof.
  induction 1 as [|s g rs ms (Hn & _) _ IH]; cbn [forallb2]; [reflexivity|].
  rewrite Hn, strcmp_refl, IH. reflexivity.
Qed.
(** check_segments. *)
Lemma check_segments_ok c m : conf_rel c m -> check_segments c m true = true.
Proof.
  intros (Hs & _ & _ & Hov & _). unfold check_segments.
  rewrite (Forall2_length Hs), Nat.eqb_refl, Hov, Z.eqb_refl.
  rewrite firstn_all2 by (rewrite (Forall2_length Hs); lia).
  rewrite (forallb2_names _ _ Hs). reflexivity.
Qed.
(** check_role, check_model, check_ignore, check_provenance, for each segment of the model. *)
Lemma check_seg_ok c m i : conf_rel c m -> (i < length (mc_seg m))%nat ->
  check_seg c (nth i (mc_seg m) mseg_d) = true.
Proof.
  intros Hc Hi. pose proof Hc as (Hs & Hok & Hnd & _).
  assert (Hg : seg_ok (nth i (mc_seg m) mseg_d)) by (rewrite Forall_forall in Hok; apply Hok, nth_In, Hi).
  destruct Hg as (Hgn & Hgl & Hgr & Hgi).
  assert (Hf : r_find c (ms_name (nth i (mc_seg m) mseg_d)) = Some i).
  { unfold r_find. rewrite (find_rel _ _ _ 0 Hs Hok Hgn). apply m_find_go_nth; auto. }
  pose proof (Forall2_nth' seg_rel _ _ rseg_d mseg_d i Hs seg_rel_d) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
  unfold check_seg, r_role, r_model, r_ignored, r_role_file, r_ignore_file, r_seg. rewrite Hf.
  rewrite H2, H3, H4, H5, H6, H8, H9.
  set (g := nth i (mc_seg m) mseg_d) in *. set (s := nth i (rc_seg c) rseg_d) in *.
  repeat (apply andb_true_iff; split).
  - destruct (ms_role_set g); cbn [andb negb]; [apply Z.eqb_refl | reflexivity].
  - destruct (ms_model_set g) eqn:Em; cbn [same_text]; [|reflexivity].
    rewrite (H7 eq_refl), strcmp_refl. reflexivity.
  - destruct (ms_ignore g); reflexivity.
  - destruct (ms_role_set g) eqn:Er; cbn [andb same_text]; [|reflexivity].
    rewrite (proj2 (Z.eqb_neq _ _) (Hgr eq_refl)). cbn [negb same_text]. rewrite strcmp_refl. reflexivity.
  - destruct (ms_ignore_set g) eqn:Ei; cbn [andb same_text]; [|reflexivity].
    rewrite (proj2 (Z.eqb_neq _ _) (Hgi eq_refl)). cbn [negb same_text]. rewrite strcmp_refl. reflexivity.
Qed.
Lemma check_segs_ok c m : conf_rel c m -> forallb (check_seg c) (mc_seg m) = true.
Proof.
  intros Hc. apply forallb_forall. intros g Hin. destruct (In_nth _ _ mseg_d Hin) as (i & Hi & <-).
  apply check_seg_ok; auto.
Qed.
(** check_refusals. *)
Lemma check_refusals_ok c m : conf_rel c m -> check_refusals c m = true.
Proof.
  intros (_ & _ & _ & _ & Href & Hkept & _). unfold check_refusals.
  rewrite Href, Z.eqb_refl, (Forall2_length Hkept), Nat.eqb_refl. reflexivity.
Qed.
(** check_address and check_knock_refused for every kept refusal. *)
Lemma check_kept_all_ok ts ks : Forall2 kept_rel ts ks -> check_kept_all ts ks = true.
Proof.
  induction 1 as [|t k ts ks (Htn & Hkn & (rest & ->) & Hknock) _ IH]; cbn [check_kept_all]; [reflexivity|].
  rewrite IH, andb_true_r. unfold check_kept.
  rewrite strlen_id by exact Hkn. rewrite strncmp_prefix by exact Hkn. cbn [Z.eqb andb].
  destruct (snd k) eqn:E; cbn [negb orb]; [|reflexivity].
  unfold strstr_found. rewrite cut_nul_id by exact Htn. apply Hknock; reflexivity.
Qed.
(** check_absent. *)
Lemma probe_ok_ok c m p : conf_rel c m -> nulfree p -> probe_ok c m p = true.
Proof.
  intros (Hs & Hok & _) Hp. unfold probe_ok, m_find.
  rewrite <- (find_rel _ _ _ 0 Hs Hok Hp).
  destruct (r_find_go (rc_seg c) p 0) as [i|] eqn:E; [reflexivity|].
  unfold absent, r_role, r_ignored, r_model, r_find. rewrite E. reflexivity.
Qed.
(** check_declared: reac_segconf_declared (R:561-580) against m_declared (H:353-371). *)
Lemma m_split_parent name p v : nulfree name -> (length name < 16)%nat -> m_split name = Some (p, v) ->
  nulfree p /\ (length p < 15)%nat.
Proof.
  intros Hn Hl H. unfold m_split in H.
  destruct (strrchr name DOT) as [di|] eqn:Hd; [|discriminate].
  apply strrchr_lt in Hd. rewrite cut_nul_id in Hd by exact Hn.
  destruct (_ || _); [discriminate|]. destruct (m_digits _ 0); [|discriminate].
  destruct (_ <? 1); [discriminate|]. destruct (forallb _ _); [|discriminate]. injection H as <- <-.
  split; [apply nulfree_firstn, Hn | rewrite length_firstn; lia].
Qed.
Lemma decl_rel rs ms tab cap a : Forall2 seg_rel rs ms -> Forall seg_ok ms ->
  r_decl_go rs tab cap a = m_decl_go ms tab cap a.
Proof.
  intros H; revert tab a; induction H as [|s g rs ms Hsg H IH]; intros tab a Hok; cbn [r_decl_go m_decl_go];
    [reflexivity|].
  inversion Hok as [|? ? (Hgn & Hgl & _) Hok']; subst.
  destruct Hsg as (Hn & _ & _ & Hig & _). rewrite Hig, Hn.
  destruct (ms_ignore g); [apply IH; exact Hok'|].
  rewrite (split_rel _ Hgn Hgl).
  destruct (m_split (ms_name g)) as [[p v]|] eqn:Hsp; [|apply IH; exact Hok'].
  destruct (m_split_parent _ _ _ Hgn Hgl Hsp) as [Hpn Hpl].
  unfold vlan_add.
  destruct (existsb (fun e => (snd e =? v) && (strcmp (fst e) p =? 0)) tab).
  - cbn [Z.ltb Z.compare]. rewrite Z.add_0_r. apply IH; exact Hok'.
  - destruct (cap <=? Z.of_nat (length tab)); [reflexivity|].
    rewrite (cut_nul_id p Hpn), (firstn_all2 (n := 15) p) by lia. rewrite IH by exact Hok'. reflexivity.
Qed.
Lemma m_decl_len ms : forall tab cap a, Z.of_nat (length tab) <= cap ->
  Z.of_nat (length (snd (m_decl_go ms tab cap a))) <= cap.
Proof.
  induction ms as [|g ms IH]; intros tab cap a H; cbn [m_decl_go]; [exact H|].
  destruct (ms_ignore g); [apply IH, H|].
  destruct (m_split (ms_name g)) as [[p v]|]; [|apply IH, H].
  destruct (existsb _ tab); [apply IH, H|].
  destruct (Z.leb_spec cap (Z.of_nat (length tab))); [cbn [snd]; exact H|].
  apply IH. rewrite length_app. cbn [length]. lia.
Qed.
Lemma forallb2_tab_refl (l : list (list Z * Z)) :
  forallb2 (fun e e' => (snd e =? snd e') && (strcmp (fst e) (fst e') =? 0)) l l = true.
Proof.
  induction l as [|e l IH]; cbn [forallb2]; [reflexivity|]. rewrite Z.eqb_refl, strcmp_refl, IH. reflexivity.
Qed.
Lemma vlans_are_refl x cap : Z.of_nat (length (snd x)) <= cap -> vlans_are x x cap = true.
Proof.
  intros H. unfold vlans_are. rewrite Z.eqb_refl, Nat.eqb_refl, forallb2_tab_refl. cbn [andb].
  apply Z.leb_le, H.
Qed.
Lemma vlan_init_len p : 0 <= p_cap p -> Z.of_nat (length (vlan_init p)) <= p_cap p.
Proof.
  intros H. unfold vlan_init.
  destruct (negb (Z.land (p_flags p) 1 =? 0) && (0 <? p_cap p)) eqn:E; cbn [length]; [|lia].
  apply andb_true_iff in E as [_ E]. apply Z.ltb_lt in E. lia.
Qed.

(** ** 14. The payload (F:31-97, H:581-601) *)

Definition byte_ok (b : Z) : Prop := 0 <= b < 256.
Lemma u8_ok inp : Forall byte_ok inp -> byte_ok (fst (fuzz_u8 inp)) /\ Forall byte_ok (snd (fuzz_u8 inp)).
Proof.
  intros H; destruct inp as [|b r]; cbn; [split; [unfold byte_ok; lia | constructor]|].
  inversion H; subst; split; assumption.
Qed.
Lemma land65535 x : 0 <= Z.land x 65535 <= 65535.
Proof.
  assert (E : Z.land x 65535 = x mod 65536)
    by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity).
  rewrite E. pose proof (Z.mod_pos_bound x 65536 ltac:(lia)). lia.
Qed.
Lemma u16_ok inp : Forall byte_ok inp -> 0 <= fst (fuzz_u16 inp) <= 65535 /\ Forall byte_ok (snd (fuzz_u16 inp)).
Proof.
  intros H. unfold fuzz_u16.
  pose proof (u8_ok inp H) as Hu. revert Hu. destruct (fuzz_u8 inp) as [lo i1]. cbn [fst snd]. intros [_ H1].
  pose proof (u8_ok i1 H1) as Hu. revert Hu. destruct (fuzz_u8 i1) as [hi i2]. cbn [fst snd]. intros [_ H2].
  split; [apply land65535 | exact H2].
Qed.
Lemma dec_files_ok k : forall inp, Forall byte_ok inp -> Forall file_ok (dec_files k inp).
Proof.
  induction k as [|k IH]; intros inp H; cbn [dec_files]; [constructor|].
  pose proof (u8_ok inp H) as Hu. revert Hu. destruct (fuzz_u8 inp) as [lb i1]. cbn [fst snd]. intros [Hb H1].
  pose proof (u16_ok i1 H1) as Hu. revert Hu. destruct (fuzz_u16 i1) as [len i2]. cbn [fst snd]. intros [Hl H2].
  unfold fuzz_take. cbv beta iota zeta. constructor.
  - unfold file_ok; cbn [f_text f_lb]. split; [apply cut_nul_nulfree|]. split; [|exact Hb].
    unfold fuzz_str. pose proof (cut_nul_len (firstn (Nat.min (Z.to_nat len) (length i2)) i2)) as Hc.
    rewrite length_firstn in Hc. lia.
  - apply IH, Forall_skipn', H2.
Qed.
Lemma decode_ok data : Forall byte_ok data -> Forall file_ok (p_files (decode data)) /\ 0 <= p_cap (decode data).
Proof.
  intros H. unfold decode.
  pose proof (u8_ok data H) as Hu. revert Hu. destruct (fuzz_u8 data) as [b0 i1]. cbn [fst snd]. intros [_ H1].
  pose proof (u8_ok i1 H1) as Hu. revert Hu. destruct (fuzz_u8 i1) as [fl i2]. cbn [fst snd]. intros [_ H2].
  pose proof (u8_ok i2 H2) as Hu. revert Hu. destruct (fuzz_u8 i2) as [b2 i3]. cbn [fst snd]. intros [_ H3].
  cbn [p_files p_cap]. split; [apply dec_files_ok, H3 | pose proof (Z.mod_pos_bound b0 40 ltac:(lia)); lia].
Qed.

(** ** 15. THE AGREEMENT THEOREM: on every input of bytes, every check_* of LLVMFuzzerTestOneInput passes. *)
Theorem segconf_agrees : segconf_agreement.
Proof.
  intros data Hd. destruct (decode_ok data Hd) as [Hf Hcap].
  unfold harness_ok, run.
  pose proof (run_rel (p_files (decode data)) rconf0 mconf0 true conf_rel0 Hf) as Hr.
  revert Hr. destruct (run_files (p_files (decode data)) rconf0 mconf0 true) as [[c m] ret]. intros [Hc ->].
  pose proof Hc as (Hs & Hok & _ & _ & _ & Hkept & _).
  rewrite (check_segments_ok c m Hc), (check_segs_ok c m Hc), (check_refusals_ok c m Hc),
          (check_kept_all_ok _ _ Hkept).
  assert (Hp : forallb (fun g => probe_ok c m (snprintf_s 18 F_probe [AS (ms_name g)])) (mc_seg m) = true).
  { apply forallb_forall. intros g _. apply probe_ok_ok; [exact Hc|].
    apply snprintf_nulfree, nulfree_forallb; vm_compute; reflexivity. }
  rewrite Hp, (probe_ok_ok c m S_nosuch Hc ltac:(apply nulfree_forallb; vm_compute; reflexivity)).
  unfold r_declared, m_declared. rewrite (decl_rel _ _ _ _ 0 Hs Hok).
  rewrite vlans_are_refl; [reflexivity|]. apply m_decl_len, vlan_init_len, Hcap.
Qed.
