/*
Cassiano Luis Flores Michel – 20204012-7
José Eduardo Rodrigues Serpa - 2020311-7
Pedro Menuzzi Mascaró – 20103702-5
 */
class CircularQueue {
    var tamanho: int;
    var inicio: int;
    var fim: int;
    var elementos: array<int>;
    ghost var fila: seq<int>;

    predicate valido() reads this, elementos {
        0 <= inicio < elementos.Length &&
        0 <= fim < elementos.Length &&
        0 <= tamanho <= elementos.Length 
    }

    constructor (cap: int)
    requires cap > 0
    ensures valido() && tamanho == 0
    {
        var newElementos := new int[cap];
        tamanho := 0;
        inicio := 0;
        fim := 0;
        elementos := newElementos;
        fila := [];
    }

    method vazia() returns (vazia: bool)
    requires valido()
    ensures vazia <==> tamanho == 0
    {
        vazia := tamanho == 0;
    }

    method numero_elementos() returns (n: int)
        requires valido()
        ensures n == tamanho
    {
        n := tamanho;
    }

    method contem(element: int) returns (contains: bool)
    requires valido()
    ensures elementos == old(elementos)
    ensures contains ==> exists i :: 0 <= i < elementos.Length && elementos[i] == element
    ensures valido()
    {
        var i := 0;

        var pertence := false;

        while(i < elementos.Length)
        invariant 0 <= i <= elementos.Length; 
        invariant elementos == old(elementos)
        invariant pertence ==> exists i :: 0 <= i < elementos.Length && elementos[i] == element
        {
            if(elementos[i] == element){
                pertence := true;
                break;
            }
            i := i + 1;
        }

        assert pertence ==> exists i :: 0 <= i < elementos.Length && elementos[i] == element;
        contains := pertence;
    }


    method adicionar(element: int)
    requires valido()
    modifies this
    ensures valido()
    ensures tamanho == old(tamanho) + 1
    {   
        var novoArray := new int[2 * elementos.Length];
        if (tamanho == elementos.Length) {
            var i := 0;
            while(i < tamanho) 
            invariant tamanho == old(tamanho);
            invariant 0 <= i <= tamanho <= elementos.Length < novoArray.Length; 
            {
                var index := inicio + i;

                novoArray[i] := elementos[index % elementos.Length];
                
                i := i + 1;
            }
            elementos := novoArray;
            inicio := 0;
            fim := tamanho;
            novoArray[fim] := element;
            fim := (fim + 1) % elementos.Length;
            tamanho := tamanho + 1;
            fila := fila + [element];
            elementos := novoArray;
        } else {
            var novoArray_igual := new int[elementos.Length];
            var i := 0;

            while(i < tamanho) 
            invariant tamanho == old(tamanho);
            invariant 0 <= i <= tamanho <= novoArray_igual.Length == elementos.Length;
            invariant 0 <= inicio < elementos.Length;
            invariant 0 <= fim < elementos.Length; 
            invariant tamanho < elementos.Length; 
            {
                novoArray_igual[i] := elementos[i];
                i := i + 1;
            }
           
            novoArray_igual[fim] := element;
            fim := (fim + 1) % novoArray_igual.Length;
            tamanho := tamanho + 1;  
            fila := fila + [element];
            elementos := novoArray_igual;
        }
        
    }

    method remover() returns (valorRemovido: int)
    requires valido()
    requires tamanho > 0
    modifies this
    ensures valido()
    ensures tamanho == old(tamanho) - 1
    ensures 0 <= old(inicio) < elementos.Length
    {
        var novoArray_igual := new int[elementos.Length];
        var i := 0;

        var removido := 0;

        while(i < tamanho) 
        invariant tamanho == old(tamanho);
        invariant 0 <= i <= tamanho <= novoArray_igual.Length == elementos.Length;
        invariant 0 <= inicio < elementos.Length;
        invariant 0 <= fim < elementos.Length; 
        invariant removido == 0
        {
            if(i != inicio){
                novoArray_igual[i] := elementos[i];
            }
            i := i + 1;
        }

        removido := elementos[inicio];
        assert removido == elementos[inicio];
        inicio := (inicio + 1) % elementos.Length;
        tamanho := tamanho - 1;
        elementos := novoArray_igual;
        valorRemovido := removido;
    }   

}

method main()
{
    var fila := new CircularQueue(5);
    var tamanho := fila.numero_elementos();
    var vazia := fila.vazia();

    assert tamanho == 0;
    assert vazia;
    
    fila.adicionar(1);
    fila.adicionar(2);
    fila.adicionar(3);

    var tamanho_depois_de_adicionar := fila.numero_elementos();
    var vazia_depois_de_adicionar := fila.vazia();
    var contem_elemento := fila.contem(2);

    assert tamanho_depois_de_adicionar == 3;
    assert !vazia_depois_de_adicionar;

    fila.adicionar(4);
    fila.adicionar(5);
    fila.adicionar(6);
    fila.adicionar(7);

    var tamanho_depois_de_realocar := fila.numero_elementos();

    assert tamanho_depois_de_realocar == 7;

    var valor_removido := fila.remover();
    valor_removido := fila.remover();
    var tamanho_depois_de_remover := fila.numero_elementos();

    assert tamanho_depois_de_remover == 5;
    
}