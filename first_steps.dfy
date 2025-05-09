// Filtered on Freitag 2025-Mai-09 at 15:11:12 by Tippfilter 0.5-rc5-1-g51cbede (development or dirty build)
method betrag(x: int) returns (ergebnis: int)
  ensures ergebnis >= 0
  ensures ergebnis == x || ergebnis == -x
  {
    if x >= 0 {
        return x;
    } else {
        return -x;
    }
  }

/*
method max(x: int, y : int) returns (max: int)

  {
    return -23;
    // TODO!
  }

method xor(x: bool, y: bool) returns (z: bool)
{
    return false;
    // TODO!
}


method genus(substantiv: string) returns (genus: char)
  requires |substantiv| > 2
{
}  


method enthaelt(zahlen: array<int>, gesucht: int) returns (gefunden: bool)
  {
    {
      if zahlen[pos] == gesucht {
        return true;
      }
    }
    return false; 
  }

method enthaelt_Abgewickelt(zahlen: array<int>, gesucht: int) returns (gefunden: bool)
  requires zahlen.Length == 3
  ensures
    (exists index :: (0 <= index < zahlen.Length && zahlen[index] == gesucht)) 
    == gefunden
  {
    var pos := 0;
    if zahlen[pos] == gesucht {
        return true;
    }
    assert zahlen[0] != gesucht;
    pos := pos + 1;

    if zahlen[pos] == gesucht {
        return true;
        assert zahlen[0] != gesucht && zahlen[1] == gesucht;
    }
    assert zahlen[0] != gesucht;
    assert zahlen[1] != gesucht;
    pos := pos + 1;

    if zahlen[pos] == gesucht {
        return true;
    }
    assert zahlen[0] != gesucht;
    assert zahlen[1] != gesucht;
    assert zahlen[2] != gesucht;
    pos := pos + 1;

    return false; 
  }

method enthaeltRek(zahlen: array<int>, abIdx: int, gesucht: int) returns (gefunden: bool)
  requires 0 <= abIdx <= zahlen.Length
  requires ! (exists i | 0 <= i < abIdx         :: zahlen[i] == gesucht)
  ensures    (exists i | 0 <= i < zahlen.Length :: zahlen[i] == gesucht) <==> gefunden
  //requires forall i | 0 <= i < abIdx         :: zahlen[i] != gesucht
  decreases zahlen.Length - abIdx
  {
    if abIdx == zahlen.Length {
      return false;
    }
    if zahlen[abIdx] == gesucht {
      return true;
    }
    gefunden := enthaeltRek(zahlen, abIdx +1, gesucht);
  }


method indexVon(zahlen: array<int>, gesucht: int) returns (gefundenBei: int)
ensures gefundenBei == -1 <==> (forall i|0 <= i < zahlen.Length :: zahlen[i] != gesucht)
ensures gefundenBei != -1 <==> (0 <= gefundenBei < zahlen.Length && zahlen[gefundenBei] == gesucht)
{
   var suchindex := 0;
   while suchindex < zahlen.Length
   invariant suchindex <= zahlen.Length 
   invariant forall i|0 <= i < suchindex :: zahlen[i] != gesucht
   // decreases zahlen.Length - suchindex
   {
     if zahlen[suchindex] == gesucht {
       return suchindex;
     }
     suchindex := suchindex + 1;
   }
   gefundenBei := -1;
}

method istPalindrom(text: string) returns (istPalindrom: bool)
ensures (forall i | 0 <= i < |text| /2 :: text[i] == text[|text| - 1 - i ]) == istPalindrom
{
  if |text| <= 1 {
    return true;
  }
  var iLinks  := 0;
  var iRechts := |text| -1;
  
  while iLinks <= |text| / 2 -1 && iRechts >= |text| /2
//  invariant 0 <= iLinks <= |text| / 2
  invariant |text| /2 -1 <= iRechts <= |text| -1
  invariant iLinks + iRechts == |text| -1
  invariant forall l | 0 <= l < iLinks  :: text[l] == text[|text| - 1 - l] 
  {
    if text[iLinks] != text[iRechts] {
      return false;
    }
    iLinks, iRechts := iLinks + 1, iRechts - 1;
   }
  istPalindrom := true;
}