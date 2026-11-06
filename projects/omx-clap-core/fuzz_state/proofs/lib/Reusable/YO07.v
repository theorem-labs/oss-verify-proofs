(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia FMapPositive.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition zmap := PositiveMap.t Z.
Definition zm_empty : zmap := PositiveMap.empty Z.
Definition zkey (k : Z) : positive := Z.to_pos (k + 1).
Definition zm_get (m : zmap) (k : Z) : Z := match PositiveMap.find (zkey k) m with Some v => v | None => 0 end.
Definition zm_set (m : zmap) (k v : Z) : zmap := PositiveMap.add (zkey k) v m.
Fixpoint zm_clear (m : zmap) (base : Z) (n : nat) : zmap :=
match n with O => m | S n' => zm_clear (PositiveMap.remove (zkey (base + Z.of_nat n')) m) base n' end.
Definition flag (a b : Z) : bool := negb (Z.land a b =? 0).
Definition le_bytes (bs : list Z) : Z := fold_right (fun b acc => b + 256 * acc) 0 bs.
Definition u16le (v : Z) : list Z := [v mod 256; (v / 256) mod 256].
Definition zeros (n : Z) : list Z := repeat 0 (Z.to_nat n).
Fixpoint np2_aux (fuel : nat) (n p : Z) : Z := match fuel with O => p | S f => if 2 ^ p <? n then np2_aux f n (p + 1) else p end.
Definition calcNextPower2Ex (n : Z) : Z := np2_aux 17 n 0.
Definition calcInitCodeLen (n : Z) : Z := let i := calcNextPower2Ex n in if i <? 3 then 3 else i + 1.
Definition MAX_DICT_LEN : Z := 4096.
Record lzw_st := mkLzw {
l_init : zmap;
l_lmap : zmap;
l_lcol : zmap;
l_lidx : zmap;
l_tmap : zmap;
l_dictPos : Z;
l_mapPos : Z;
l_codes : list Z
}.
Definition lzw_reset (L : Z) (s : lzw_st) : lzw_st := mkLzw zm_empty zm_empty zm_empty zm_empty (l_tmap s) (L + 2) 1 (L :: l_codes s).
Definition lzw_emit (c : Z) (s : lzw_st) : lzw_st := mkLzw (l_init s) (l_lmap s) (l_lcol s) (l_lidx s) (l_tmap s) (l_dictPos s) (l_mapPos s) (c :: l_codes s).
Definition lzw_add_init (L parent colour : Z) (s : lzw_st) : lzw_st :=
mkLzw (zm_set (l_init s) (parent * L + colour) (l_dictPos s)) (l_lmap s) (l_lcol s) (l_lidx s) (l_tmap s) (l_dictPos s + 1) (l_mapPos s) (l_codes s).
Definition lzw_add_child (L parent colour : Z) (s : lzw_st) : lzw_st :=
let idx := l_dictPos s in
let mp := zm_get (l_lmap s) parent in
if mp =? 0 then
if zm_get (l_lidx s) parent =? 0 then
mkLzw (l_init s) (l_lmap s) (zm_set (l_lcol s) parent colour) (zm_set (l_lidx s) parent idx) (l_tmap s) (idx + 1) (l_mapPos s) (l_codes s)
else
let row := (l_mapPos s - 1) * L in
mkLzw (l_init s) (zm_set (l_lmap s) parent (l_mapPos s)) (l_lcol s) (l_lidx s)
(zm_set (zm_clear (l_tmap s) row (Z.to_nat L)) (row + colour) idx) (idx + 1) (l_mapPos s + 1) (l_codes s)
else mkLzw (l_init s) (l_lmap s) (l_lcol s) (l_lidx s) (zm_set (l_tmap s) ((mp - 1) * L + colour) idx) (idx + 1) (l_mapPos s) (l_codes s).
Definition lzw_child (L parent colour : Z) (s : lzw_st) : Z :=
if negb (zm_get (l_lidx s) parent =? 0) && (zm_get (l_lcol s) parent =? colour) then zm_get (l_lidx s) parent
else let mp := zm_get (l_lmap s) parent in if mp =? 0 then 0 else zm_get (l_tmap s) ((mp - 1) * L + colour).
Fixpoint lzw_run (L : Z) (s : lzw_st) (parent : Z) (atroot : bool) (rest : list Z) : option lzw_st :=
match rest with
| [] => Some (lzw_emit parent s)
| nxt :: rest' =>
if L <=? nxt then None
else
let c := if atroot then zm_get (l_init s) (parent * L + nxt) else lzw_child L parent nxt s in
if c =? 0 then
let s1 := lzw_emit parent s in
let s2 := if l_dictPos s1 <? MAX_DICT_LEN then (if atroot then lzw_add_init L parent nxt s1 else lzw_add_child L parent nxt s1) else lzw_reset L s1 in
lzw_run L s2 nxt true rest'
else lzw_run L s c false rest'
end.
Definition lzw_codes (L : Z) (img : list Z) : option (list Z) :=
match img with
| [] => None
| p0 :: rest =>
if L <=? p0 then None
else match lzw_run L (lzw_reset L (mkLzw zm_empty zm_empty zm_empty zm_empty zm_empty 0 0 [])) p0 true rest with
| None => None
| Some s => Some (rev ((L + 1) :: l_codes s))
end
end.
Record pk_st := mkPk { p_bl : list Z; p_off : Z; p_len : Z; p_n : Z; p_dict : Z; p_corr : bool }.
Definition or_head (bl : list Z) (v : Z) : list Z := match bl with [] => [v] | h :: t => Z.lor h v :: t end.
Definition pk_step (L initCodeLen : Z) (s : pk_st) (code : Z) : pk_st :=
let grow := (p_len s <? 12) && (((p_n s - L) mod 2 ^ 32) =? p_dict s) in
let len := if grow then p_len s + 1 else p_len s in
let n := if grow then (p_n s * 2) mod 65536 else p_n s in
let off := p_off s in
let bl1 := or_head (p_bl s) ((code * 2 ^ off) mod 256) in
let tot := len + off in
let b1 := (code / 2 ^ (8 - off)) mod 256 in
let b2 := (code / 2 ^ (16 - off)) mod 256 in
let '(bl2, corr) := if tot <? 8 then (bl1, false)
else if tot =? 8 then (0 :: bl1, true)
else if tot <? 16 then (b1 :: bl1, false)
else if tot =? 16 then (0 :: b1 :: bl1, true)
else (b2 :: b1 :: bl1, false) in
if code =? L then mkPk bl2 (tot mod 8) initCodeLen ((2 * L) mod 65536) 1 corr
else mkPk bl2 (tot mod 8) len n (p_dict s + 1) corr.
Definition create_byte_list (L initCodeLen : Z) (codes : list Z) : list Z :=
let s := fold_left (pk_step L initCodeLen) codes (mkPk [0] 0 initCodeLen ((2 * L) mod 65536) 1 false) in
rev (if p_corr s then tl (p_bl s) else p_bl s).
Fixpoint blocks255 (fuel : nat) (l : list Z) : list Z :=
match fuel with
| O => [0]
| S f => match l with
| [] => [0]
| _ => let b := firstn 255 l in Z.of_nat (length b) :: b ++ blocks255 f (skipn 255 l)
end
end.
Definition lzw_stream (L initCodeLen : Z) (img : list Z) : option (list Z) :=
match lzw_codes L img with
| None => None
| Some codes => let bl := create_byte_list L initCodeLen codes in Some (blocks255 (S (length bl)) bl)
end.
Definition pal_pow (n : Z) : Z := Z.max 1 (calcNextPower2Ex n).
Definition raw_header (width height sizeGCT : Z) (gct : list Z) (rattr numLoops : Z) : list Z :=
[71; 73; 70; 56; 57; 97] ++ u16le width ++ u16le height ++ [if sizeGCT =? 0 then 0 else 128 + (pal_pow sizeGCT - 1); 0; 0]
++ (if sizeGCT =? 0 then [] else firstn (Z.to_nat (sizeGCT * 3)) gct ++ zeros (((2 ^ pal_pow sizeGCT - sizeGCT) * 3) mod 65536))
++ (if flag rattr 1 && negb (flag rattr 2) then [33; 255; 11; 78; 69; 84; 83; 67; 65; 80; 69; 50; 46; 48; 3; 1] ++ u16le numLoops ++ [0] else []).
Fixpoint rows_of (fuel : nat) (w : nat) (l : list Z) : list (list Z) :=
match fuel with O => [] | S f => match l with [] => [] | _ => firstn w l :: rows_of f w (skipn w l) end end.
Fixpoint pick_rows (rows : list (list Z)) (i : nat) (start step : nat) : list Z :=
match rows with
| [] => []
| r :: rs => (if (start <=? i)%nat && Nat.eqb ((i - start) mod step) 0 then r else []) ++ pick_rows rs (S i) start step
end.
Definition interlace (w : Z) (img : list Z) : list Z :=
let rows := rows_of (S (length img)) (Z.to_nat w) img in
pick_rows rows 0 0 8 ++ pick_rows rows 0 4 8 ++ pick_rows rows 0 2 4 ++ pick_rows rows 0 1 2.
Definition R_OK : Z := 0. Definition R_ERROR : Z := -1. Definition R_EINDEX : Z := 5. Definition R_PENDING : Z := 6.
Definition raw_addframe (ganim : bool) (sizeGCT rcur : Z) (img : list Z) (rfattr width height top lf delay sizeLCT : Z) (lct : list Z) (disposal transIndex : Z) : Z * list Z :=
if negb (rcur =? R_OK) && negb (rcur =? R_PENDING) then (rcur, [])
else if 256 <? sizeLCT then (R_ERROR, [])
else
let useLCT := negb (sizeLCT =? 0) in
let inter := flag rfattr 2 in
let packed := (if useLCT then 128 + (pal_pow sizeLCT - 1) else 0) + (if inter then 64 else 0) in
let numEff0 := if useLCT then sizeLCT else sizeGCT in
let numEff := if ganim && flag rfattr 1 && (numEff0 <=? transIndex) then transIndex + 1 else numEff0 in
let initCodeLen := calcInitCodeLen numEff in
let L := 2 ^ (initCodeLen - 1) in
match lzw_stream L initCodeLen (if inter then interlace width img else img) with
| None => (R_EINDEX, [])
| Some raster =>
(R_OK,
(if ganim || flag rfattr 1 then [33; 249; 4; (if flag rfattr 1 then Z.lor (disposal mod 256) 1 else disposal mod 256)] ++ u16le delay ++ [if flag rfattr 1 then transIndex else 0; 0] else [])
++ [44] ++ u16le lf ++ u16le top ++ u16le width ++ u16le height ++ [packed]
++ (if useLCT then firstn (Z.to_nat (sizeLCT * 3)) lct ++ zeros (((2 ^ pal_pow sizeLCT - sizeLCT) * 3) mod 65536) else [])
++ [initCodeLen - 1] ++ raster)
end.
Record frame := mkFr {
f_attr : Z; f_gen : Z; f_delay : Z; f_nlp : Z; f_lpal : list Z; f_img : list Z;
f_ctrans : Z;
f_disp : Z; f_trans : Z }.
Definition set_gen (f : frame) (g : Z) : frame := mkFr (f_attr f) g (f_delay f) (f_nlp f) (f_lpal f) (f_img f) (f_ctrans f) (f_disp f) (f_trans f).
Definition set_disp (f : frame) (d : Z) : frame := mkFr (f_attr f) (f_gen f) (f_delay f) (f_nlp f) (f_lpal f) (f_img f) (f_ctrans f) d (f_trans f).
Definition set_delay (f : frame) (d : Z) : frame := mkFr (f_attr f) (f_gen f) d (f_nlp f) (f_lpal f) (f_img f) (f_ctrans f) (f_disp f) (f_trans f).
Definition clr (v bits : Z) : Z := Z.land v (Z.lnot bits).
Record gcfg := mkG { g_w : Z; g_h : Z; g_attr : Z; g_gen : Z; g_ngp : Z; g_gpal : list Z }.
Definition col3 (pal : list Z) (i : Z) : list Z := firstn 3 (skipn (Z.to_nat (3 * i)) pal).
Definition list_eqb (a b : list Z) : bool := (length a =? length b)%nat && forallb (fun p => fst p =? snd p) (combine a b).
Definition cmp_pixel (g : gcfg) (cur bef : frame) (iCur iBef : Z) : bool :=
if flag (f_attr cur) 4 && (iCur =? f_ctrans cur) then false
else if flag (f_attr bef) 4 && (iBef =? f_ctrans bef) then true
else
let sB := if flag (f_attr bef) 1 then f_nlp bef else g_ngp g in
let sC := if flag (f_attr cur) 1 then f_nlp cur else g_ngp g in
if (sB <=? iBef) || (sC <=? iCur) then true
else negb (list_eqb (col3 (if flag (f_attr bef) 1 then f_lpal bef else g_gpal g) iBef) (col3 (if flag (f_attr cur) 1 then f_lpal cur else g_gpal g) iCur)).
Definition px_ne (g : gcfg) (cur bef : frame) : Z -> Z -> bool :=
if negb (flag (f_attr bef) 1) && negb (flag (f_attr cur) 1) && negb (flag (f_attr bef) 4) && negb (flag (f_attr cur) 4)
then (fun c b => negb (c =? b)) else cmp_pixel g cur bef.
Fixpoint first_true (l : list bool) (i : Z) : option Z := match l with [] => None | b :: t => if b then Some i else first_true t (i + 1) end.
Fixpoint last_true (l : list bool) (i : Z) (acc : option Z) : option Z := match l with [] => acc | b :: t => last_true t (i + 1) (if b then Some i else acc) end.
Definition omin (a b : option Z) : option Z := match a, b with Some x, Some y => Some (Z.min x y) | Some x, None => Some x | None, y => y end.
Definition omax (a b : option Z) : option Z := match a, b with Some x, Some y => Some (Z.max x y) | Some x, None => Some x | None, y => y end.
Definition diff_area (g : gcfg) (cur bef : frame) : option (Z * Z * Z * Z) :=
let w := Z.to_nat (g_w g) in
let dm := map (fun rb => map (fun p => px_ne g cur bef (fst p) (snd p)) (combine (fst rb) (snd rb)))
(combine (rows_of (S (length (f_img cur))) w (f_img cur)) (rows_of (S (length (f_img bef))) w (f_img bef))) in
let rowany := map (existsb (fun b => b)) dm in
match first_true rowany 0, last_true rowany 0 None with
| Some top, Some bot =>
let band := firstn (Z.to_nat (bot + 1 - top)) (skipn (Z.to_nat top) dm) in
match fold_right (fun r acc => omin (first_true r 0) acc) None band, fold_right (fun r acc => omax (last_true r 0 None) acc) None band with
| Some lf, Some rt => Some (rt + 1 - lf, bot + 1 - top, top, lf)
| _, _ => None
end
| _, _ => None
end.
Definition window (W : Z) (img : list Z) (width height top lf : Z) : list Z :=
flat_map (fun r => firstn (Z.to_nat width) (skipn (Z.to_nat lf) r))
(firstn (Z.to_nat height) (skipn (Z.to_nat top) (rows_of (S (length img)) (Z.to_nat W) img))).
Definition flush_frame (g : gcfg) (rcur : Z) (cur : frame) (bef : option frame) : Z * list Z :=
let useLCT := flag (f_attr cur) 1 in
let hasAlpha := flag (g_attr g) 8 || flag (f_attr cur) 2 in
let hasSet := flag (f_attr cur) 4 in
let gen0 := f_gen cur in
let gen1 := match bef with None => clr gen0 3 | Some _ => if hasAlpha then clr gen0 3 else gen0 end in
let gen2 := if hasSet then clr gen1 1 else gen1 in
let npal := if useLCT then f_nlp cur else g_ngp g in
let gen3 := if npal =? 256 then clr gen2 1 else gen2 in
match bef with
| None => raw_addframe (flag (g_attr g) 2) (if flag (g_attr g) 4 then 0 else g_ngp g) rcur (f_img cur)
((if hasAlpha || hasSet then 1 else 0) + (if flag (f_attr cur) 8 then 2 else 0)) (g_w g) (g_h g) 0 0 (f_delay cur) (if useLCT then f_nlp cur else 0) (f_lpal cur) (f_disp cur) (f_trans cur)
| Some b =>
let '(width, height, top, lf) :=
if flag gen3 2 then match diff_area g cur b with Some d => d | None => (1, 1, 0, 0) end else (g_w g, g_h g, 0, 0) in
let tmp := if flag gen3 2 then window (g_w g) (f_img cur) width height top lf else f_img cur in
let p := Z.max 2 (calcNextPower2Ex npal) in
let t0 := (2 ^ p - 1) mod 256 in
let tOpt := if t0 <? npal then (2 ^ (p + 1) - 1) mod 256 else t0 in
let transIndex := if flag gen3 1 then tOpt else f_trans cur in
let img := if flag gen3 1
then map (fun pq => if cmp_pixel g cur b (fst pq) (snd pq) then fst pq else transIndex) (combine tmp (window (g_w g) (f_img b) width height top lf))
else tmp in
raw_addframe (flag (g_attr g) 2) (if flag (g_attr g) 4 then 0 else g_ngp g) rcur img
((if hasAlpha || flag gen3 1 || hasSet then 1 else 0) + (if flag (f_attr cur) 8 then 2 else 0)) width height top lf (f_delay cur) (if useLCT then f_nlp cur else 0) (f_lpal cur) (f_disp cur) transIndex
end.
Definition C_OK : Z := 0. Definition C_ERROR : Z := -1. Definition C_PENDING : Z := 6.
Record gif_st := mkS { s_q0 : option frame; s_q1 : option frame; s_q2 : option frame; s_ihead : Z; s_cur : Z; s_rcur : Z; s_out : list (list Z) }.
Definition q_get (s : gif_st) (i : Z) : option frame := if i =? 0 then s_q0 s else if i =? 1 then s_q1 s else s_q2 s.
Definition q_set (s : gif_st) (i : Z) (f : option frame) : gif_st :=
if i =? 0 then mkS f (s_q1 s) (s_q2 s) (s_ihead s) (s_cur s) (s_rcur s) (s_out s)
else if i =? 1 then mkS (s_q0 s) f (s_q2 s) (s_ihead s) (s_cur s) (s_rcur s) (s_out s)
else mkS (s_q0 s) (s_q1 s) f (s_ihead s) (s_cur s) (s_rcur s) (s_out s).
Definition with_cur (s : gif_st) (c : Z) : gif_st := mkS (s_q0 s) (s_q1 s) (s_q2 s) (s_ihead s) c (s_rcur s) (s_out s).
Definition omap (fn : frame -> frame) (o : option frame) : option frame := match o with Some f => Some (fn f) | None => None end.
Definition new_frame (g : gcfg) (attr gen delay ctrans nlp : Z) (lpal img : list Z) : frame :=
mkFr attr gen delay nlp lpal img (if flag attr 6 then ctrans else 0)
(if flag (g_attr g) 8 then 8 else 4) (if flag attr 2 || flag attr 4 then ctrans else 0).
Definition add_frame (g : gcfg) (s : gif_st) (attr gen delay ctrans nlp : Z) (lpal img : list Z) : gif_st :=
if negb (s_cur s =? C_OK) && negb (s_cur s =? C_PENDING) then s
else
let hasAlpha := flag (g_attr g) 8 || flag attr 2 in
let hasSet := flag attr 4 in
if (hasAlpha && hasSet) || (flag (g_attr g) 8 && flag attr 2) || (negb (flag attr 1) && flag (g_attr g) 4) then with_cur s C_ERROR
else
let nf := new_frame g attr gen delay ctrans nlp lpal img in
let merged :=
match q_get s (s_ihead s) with
| Some hd =>
let fd := delay + f_delay hd in
if (fd <=? 65535) && negb (flag (g_gen g) 1) then
let same := if negb (flag attr 1) && negb (flag (f_attr hd) 1) && negb (flag attr 4) && negb (flag (f_attr hd) 4)
then list_eqb img (f_img hd)
else forallb (fun pq => negb (cmp_pixel g nf hd (fst pq) (snd pq))) (combine img (f_img hd)) in
if same then Some (q_set s (s_ihead s) (Some (set_delay hd fd))) else None
else None
| None => None
end in
match merged with
| Some s' => s'
| None =>
let i0 := if match q_get s (s_ihead s) with None => true | Some _ => false end then s_ihead s
else if (s_ihead s <? 2) && match s_q2 s with None => true | Some _ => false end then 2 else 3 in
let '(s1, i, failed) :=
if i0 =? 3 then
match s_q1 s with
| Some f1 =>
let '(r, bytes) := flush_frame g (s_rcur s) f1 (s_q0 s) in
let s' := mkS (s_q0 s) (s_q1 s) (s_q2 s) (s_ihead s) (s_cur s) (if negb (s_rcur s =? R_OK) && negb (s_rcur s =? R_PENDING) then s_rcur s else r) (if r =? C_OK then s_out s ++ [bytes] else s_out s) in
if r =? C_OK then (mkS (s_q1 s') (s_q2 s') None (s_ihead s') (s_cur s') (s_rcur s') (s_out s'), 2, false)
else (mkS None (s_q1 s') (s_q2 s') (s_ihead s') r (s_rcur s') (s_out s'), 2, true)
| None => (s, 2, false)
end
else (s, i0, false) in
if failed then s1
else
let s2 := q_set s1 i (Some nf) in
let s3 := mkS (s_q0 s2) (s_q1 s2) (s_q2 s2) i (s_cur s2) (s_rcur s2) (s_out s2) in
let s4 := if flag (g_attr g) 8 then q_set s3 (i - 1) (omap (fun f => set_disp (set_gen f (clr (f_gen f) 3)) 8) (q_get s3 (i - 1))) else s3 in
let s5 := if flag attr 2 then q_set s4 (i - 1) (omap (fun f => set_disp (set_gen f (clr (f_gen f) 2)) 8) (q_get s4 (i - 1))) else s4 in
with_cur s5 C_OK
end.
Definition close_gif (g : gcfg) (s : gif_st) : list (list Z) :=
let fl (st : gif_st * bool) (i : Z) : gif_st * bool :=
let '(s0, stop) := st in
if stop then st
else match q_get s0 i with
| None => st
| Some f =>
let '(r, bytes) := flush_frame g (s_rcur s0) f (q_get s0 (i - 1)) in
(mkS (s_q0 s0) (s_q1 s0) (s_q2 s0) (s_ihead s0) (s_cur s0) r (if r =? C_OK then s_out s0 ++ [bytes] else s_out s0), negb (r =? C_OK))
end in
let s1 := if s_cur s =? C_OK then fst (fl (fl (s, false) 1) 2) else s in
s_out s1.
Definition rd (s : list Z) (n : Z) : bool * list Z * list Z :=
if (Z.of_nat (length s) <? n) then (true, [], []) else (false, firstn (Z.to_nat n) s, skipn (Z.to_nat n) s).
Fixpoint frames_loop (fuel : nat) (g : gcfg) (st : gif_st) (s : list Z) : gif_st :=
match fuel with
| O => st
| S fuel' =>
let '(e1, a, s1) := rd s 2 in let '(e2, ge, s2) := rd s1 2 in let '(e3, d, s3) := rd s2 2 in let '(e4, t, s4) := rd s3 1 in let '(e5, n, s5) := rd s4 2 in
let attr := le_bytes a in let nlp := le_bytes n in
let '(e6, lpal, s6) := if flag attr 1 then rd s5 (nlp * 3) else (false, [], s5) in
let '(e7, img, s7) := rd s6 (g_w g * g_h g) in
if e1 || e2 || e3 || e4 || e5 || e6 || e7 then st
else frames_loop fuel' g (add_frame g st attr (le_bytes ge) (le_bytes d) (le_bytes t) nlp lpal img) s7
end.
Definition ff_chunks (payload : list Z) : option (list (list Z)) :=
let '(e1, w, s1) := rd payload 2 in let '(e2, h, s2) := rd s1 2 in let '(e3, a, s3) := rd s2 4 in let '(e4, ge, s4) := rd s3 4 in let '(e5, n, s5) := rd s4 2 in
let width := le_bytes w in let height := le_bytes h in let attr := le_bytes a in let ngp := le_bytes n in
let '(e6, gpal, s6) := if flag attr 4 then (false, [], s5) else rd s5 (ngp * 3) in
if e1 || e2 || e3 || e4 || e5 || e6 then None
else if 100000000 <? width * height then None
else if (width =? 0) || (height =? 0) then None
else if 256 <? (if flag attr 4 then 0 else ngp) then Some []
else
let g := mkG width height attr (le_bytes ge) ngp gpal in
let rattr := (if flag attr 2 then 1 else 0) + (if flag attr 16 then 2 else 0) in
let st0 := mkS None None None 1 C_PENDING R_PENDING [raw_header width height (if flag attr 4 then 0 else ngp) gpal rattr 0] in
Some (close_gif g (frames_loop 16 g st0 s6)).
Definition file_of_chunks (cs : list (list Z)) : list Z := match cs with [] => [] | _ => concat cs ++ [59] end.
Definition ff_output (payload : list Z) : option (list Z) := option_map file_of_chunks (ff_chunks payload).
Definition ff_output_cut (payload : list Z) (k : nat) : option (list Z) := option_map (fun cs => file_of_chunks (firstn (S k) cs)) (ff_chunks payload).
Definition ff_contents (payload : list Z) (bytes : list Z) : Prop :=
exists cs, ff_chunks payload = Some cs /\ (bytes = [] \/ exists k, bytes = file_of_chunks (firstn (S k) cs)).
Lemma ff_output_is_content : forall payload bytes, ff_output payload = Some bytes -> ff_contents payload bytes.
Proof.
intros payload bytes H. unfold ff_output in H. destruct (ff_chunks payload) as [cs|] eqn:E; [|discriminate]. injection H as <-.
exists cs. split; [exact E|]. right. exists (length cs). rewrite firstn_all2 by lia. reflexivity.
Qed.
